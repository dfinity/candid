use super::analysis::{chase_actor, infer_rec};
use crate::{
    configs::{ConfigState, ConfigTree, Configs, StateElem},
    Deserialize,
};
use candid::pretty::utils::*;
use candid::types::{Field, Function, Label, SharedLabel, Type, TypeEnv, TypeInner};
use convert_case::{Case, Casing};
use pretty::RcDoc;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Default, Deserialize, Clone, Debug)]
pub struct BindingConfig {
    name: Option<String>,
    use_type: Option<String>,
    attributes: Option<String>,
    visibility: Option<String>,
}
impl ConfigState for BindingConfig {
    fn merge_config(&mut self, config: &Self, elem: Option<&StateElem>, _is_recursive: bool) {
        self.name.clone_from(&config.name);
        // match use_type can survive across types, so that label.use_type works
        if !matches!(elem, Some(StateElem::Label(_))) {
            if let Some(use_type) = &config.use_type {
                self.use_type = Some(use_type.clone());
            }
        } else {
            self.use_type.clone_from(&config.use_type);
        }
        // matched attributes can survive across labels, so that record.attributes works
        if matches!(elem, Some(StateElem::Label(_))) {
            if let Some(attr) = &config.attributes {
                self.attributes = Some(attr.clone());
            }
        } else {
            self.attributes.clone_from(&config.attributes);
        }
        if config.visibility.is_some() {
            self.visibility.clone_from(&config.visibility);
        }
    }
    fn update_state(&mut self, _elem: &StateElem) {}
    fn restore_state(&mut self, _elem: &StateElem) {}
}
pub struct State<'a> {
    state: crate::configs::State<'a, BindingConfig>,
    recs: RecPoints<'a>,
}

type RecPoints<'a> = BTreeSet<&'a str>;
// The definition of tuple is language specific.
pub(crate) fn is_tuple(fs: &[Field]) -> bool {
    if fs.is_empty() {
        return false;
    }
    !fs.iter()
        .enumerate()
        .any(|(i, field)| field.id.get_id() != (i as u32))
}
static KEYWORDS: [&str; 51] = [
    "as", "break", "const", "continue", "crate", "else", "enum", "extern", "false", "fn", "for",
    "if", "impl", "in", "let", "loop", "match", "mod", "move", "mut", "pub", "ref", "return",
    "self", "Self", "static", "struct", "super", "trait", "true", "type", "unsafe", "use", "where",
    "while", "async", "await", "dyn", "abstract", "become", "box", "do", "final", "macro",
    "override", "priv", "typeof", "unsized", "virtual", "yield", "try",
];
fn ident_(id: &str, case: Option<Case>) -> (RcDoc, bool) {
    if id.is_empty()
        || id.starts_with(|c: char| !c.is_ascii_alphabetic() && c != '_')
        || id.chars().any(|c| !c.is_ascii_alphanumeric() && c != '_')
    {
        return (RcDoc::text(format!("_{}_", candid::idl_hash(id))), true);
    }
    let (is_rename, id) = if let Some(case) = case {
        let new_id = id.to_case(case);
        (new_id != id, new_id)
    } else {
        (false, id.to_owned())
    };
    if ["crate", "self", "super", "Self", "Result", "Principal"].contains(&id.as_str()) {
        (RcDoc::text(format!("{id}_")), true)
    } else if KEYWORDS.contains(&id.as_str()) {
        (RcDoc::text(format!("r#{id}")), is_rename)
    } else {
        (RcDoc::text(id), is_rename)
    }
}
fn ident(id: &str, case: Option<Case>) -> RcDoc {
    ident_(id, case).0
}
fn pp_vis<'a>(vis: &Option<String>) -> RcDoc<'a> {
    match vis {
        Some(vis) if vis.is_empty() => RcDoc::nil(),
        Some(vis) => RcDoc::text(vis.clone()).append(" "),
        None => RcDoc::text("pub "),
    }
}
impl<'a> State<'a> {
    fn pp_ty<'b>(&mut self, ty: &'b Type, is_ref: bool) -> RcDoc<'b> {
        use TypeInner::*;
        let elem = StateElem::Type(ty);
        let old = self.state.push_state(&elem);
        let res = if let Some(t) = &self.state.config.use_type {
            RcDoc::text(t.clone())
        } else {
            match ty.as_ref() {
                Null => str("()"),
                Bool => str("bool"),
                Nat => str("candid::Nat"),
                Int => str("candid::Int"),
                Nat8 => str("u8"),
                Nat16 => str("u16"),
                Nat32 => str("u32"),
                Nat64 => str("u64"),
                Int8 => str("i8"),
                Int16 => str("i16"),
                Int32 => str("i32"),
                Int64 => str("i64"),
                Float32 => str("f32"),
                Float64 => str("f64"),
                Text => str("String"),
                Reserved => str("candid::Reserved"),
                Empty => str("candid::Empty"),
                Var(ref id) => {
                    let name = if let Some(name) = &self.state.config.name {
                        RcDoc::text(name.clone())
                    } else {
                        ident(id, Some(Case::Pascal))
                    };
                    if !is_ref && self.recs.contains(id.as_str()) {
                        str("Box<").append(name).append(">")
                    } else {
                        name
                    }
                }
                Principal => str("Principal"),
                Opt(ref t) => str("Option").append(enclose("<", self.pp_ty(t, is_ref), ">")),
                // It's a bit tricky to use `deserialize_with = "serde_bytes"`. It's not working for `type t = blob`
                Vec(ref t) if matches!(t.as_ref(), Nat8) => str("serde_bytes::ByteBuf"),
                Vec(ref t) => str("Vec").append(enclose("<", self.pp_ty(t, is_ref), ">")),
                Record(ref fs) => self.pp_record_fields(fs, false, is_ref),
                Variant(_) => unreachable!(), // not possible after rewriting
                Func(_) => unreachable!(),    // not possible after rewriting
                Service(_) => unreachable!(), // not possible after rewriting
                Class(_, _) => unreachable!(),
                Knot(_) | Unknown | Future => unreachable!(),
            }
        };
        self.state.pop_state(old, elem);
        res
    }
    fn pp_label<'b>(&mut self, id: &'b SharedLabel, is_variant: bool, need_vis: bool) -> RcDoc<'b> {
        let vis = if need_vis {
            pp_vis(&self.state.config.visibility)
        } else {
            RcDoc::nil()
        };
        let attr = self
            .state
            .config
            .attributes
            .clone()
            .map(|s| RcDoc::text(s).append(RcDoc::line()))
            .unwrap_or(RcDoc::nil());
        match &**id {
            Label::Named(id) => {
                let (doc, is_rename) = if let Some(name) = &self.state.config.name {
                    (RcDoc::text(name.clone()), true)
                } else {
                    let case = if is_variant { Some(Case::Pascal) } else { None };
                    ident_(id, case)
                };
                let attr = if is_rename {
                    attr.append("#[serde(rename=\"")
                        .append(id.escape_debug().to_string())
                        .append("\")]")
                        .append(RcDoc::line())
                } else {
                    attr
                };
                attr.append(vis).append(doc)
            }
            Label::Id(n) | Label::Unnamed(n) => {
                // TODO rename
                vis.append("_").append(RcDoc::as_string(n)).append("_")
            }
        }
    }
    fn pp_tuple<'b>(&mut self, fs: &'b [Field], need_vis: bool, is_ref: bool) -> RcDoc<'b> {
        let tuple = fs.iter().enumerate().map(|(i, f)| {
            let lab = i.to_string();
            let old = self.state.push_state(&StateElem::Label(&lab));
            let vis = if need_vis {
                pp_vis(&self.state.config.visibility)
            } else {
                RcDoc::nil()
            };
            let res = vis.append(self.pp_ty(&f.ty, is_ref)).append(",");
            self.state.pop_state(old, StateElem::Label(&lab));
            res
        });
        enclose("(", RcDoc::concat(tuple), ")")
    }
    fn pp_record_field<'b>(&mut self, field: &'b Field, need_vis: bool, is_ref: bool) -> RcDoc<'b> {
        let lab = field.id.to_string();
        let old = self.state.push_state(&StateElem::Label(&lab));
        let res = self
            .pp_label(&field.id, false, need_vis)
            .append(kwd(":"))
            .append(self.pp_ty(&field.ty, is_ref));
        self.state.pop_state(old, StateElem::Label(&lab));
        res
    }
    fn pp_record_fields<'b>(&mut self, fs: &'b [Field], need_vis: bool, is_ref: bool) -> RcDoc<'b> {
        let old = self.state.push_state(&StateElem::TypeStr("record"));
        let res = if is_tuple(fs) {
            // TODO check if there is no name/attr in the label subtree
            self.pp_tuple(fs, need_vis, is_ref)
        } else {
            let fields: Vec<_> = fs
                .iter()
                .map(|f| self.pp_record_field(f, need_vis, is_ref))
                .collect();
            let fields = concat(fields.into_iter(), ",");
            enclose_space("{", fields, "}")
        };
        self.state.pop_state(old, StateElem::TypeStr("record"));
        res
    }
    fn pp_variant_field<'b>(&mut self, field: &'b Field) -> RcDoc<'b> {
        let lab = field.id.to_string();
        let old = self.state.push_state(&StateElem::Label(&lab));
        let res = match field.ty.as_ref() {
            TypeInner::Null => self.pp_label(&field.id, true, false),
            TypeInner::Record(fs) => self
                .pp_label(&field.id, true, false)
                .append(self.pp_record_fields(fs, false, false)),
            _ => self.pp_label(&field.id, true, false).append(enclose(
                "(",
                self.pp_ty(&field.ty, false),
                ")",
            )),
        };
        self.state.pop_state(old, StateElem::Label(&lab));
        res
    }
    fn pp_variant_fields<'b>(&mut self, fs: &'b [Field]) -> RcDoc<'b> {
        let old = self.state.push_state(&StateElem::TypeStr("variant"));
        let fields: Vec<_> = fs.iter().map(|f| self.pp_variant_field(f)).collect();
        let fields = concat(fields.into_iter(), ",");
        let res = enclose_space("{", fields, "}");
        self.state.pop_state(old, StateElem::TypeStr("variant"));
        res
    }
    fn pp_defs(&mut self, def_list: &'a [&'a str]) -> RcDoc<'a> {
        let mut res = Vec::with_capacity(def_list.len());
        for id in def_list {
            let old = self.state.push_state(&StateElem::Label(id));
            if self.state.config.use_type.is_some() {
                self.state.pop_state(old, StateElem::Label(id));
                continue;
            }
            let ty = self.state.env.find_type(id).unwrap();
            let name = self
                .state
                .config
                .name
                .clone()
                .map(RcDoc::text)
                .unwrap_or_else(|| ident(id, Some(Case::Pascal)));
            let vis = pp_vis(&self.state.config.visibility);
            let derive = self
                .state
                .config
                .attributes
                .clone()
                .map(RcDoc::text)
                .unwrap_or(RcDoc::text("#[derive(CandidType, Deserialize)]"));
            let line = match ty.as_ref() {
                TypeInner::Record(fs) => {
                    let separator = if is_tuple(fs) {
                        RcDoc::text(";")
                    } else {
                        RcDoc::nil()
                    };
                    derive
                        .append(RcDoc::line())
                        .append(vis)
                        .append("struct ")
                        .append(name)
                        .append(" ")
                        .append(self.pp_record_fields(fs, true, false))
                        .append(separator)
                }
                TypeInner::Variant(fs) => derive
                    .append(RcDoc::line())
                    .append(vis)
                    .append("enum ")
                    .append(name)
                    .append(" ")
                    .append(self.pp_variant_fields(fs)),
                TypeInner::Func(func) => str("candid::define_function!(")
                    .append(vis)
                    .append(name)
                    .append(" : ")
                    .append(self.pp_ty_func(func))
                    .append(");"),
                TypeInner::Service(serv) => str("candid::define_service!(")
                    .append(vis)
                    .append(name)
                    .append(" : ")
                    .append(self.pp_ty_service(serv))
                    .append(");"),
                _ => {
                    if self.recs.contains(id) {
                        derive
                            .append(RcDoc::line())
                            .append(vis)
                            .append("struct ")
                            .append(name)
                            .append(enclose("(", self.pp_ty(ty, false), ")"))
                            .append(";")
                    } else {
                        vis.append(kwd("type"))
                            .append(name)
                            .append(" = ")
                            .append(self.pp_ty(ty, false))
                            .append(";")
                    }
                }
            };
            self.state.pop_state(old, StateElem::Label(id));
            res.push(line)
        }
        lines(res.into_iter())
    }
    fn pp_args<'b>(&mut self, args: &'b [Type], prefix: &'b str) -> RcDoc<'b> {
        let doc: Vec<_> = args
            .iter()
            .enumerate()
            .map(|(i, t)| {
                let lab = format!("{prefix}{i}");
                let old = self.state.push_state(&StateElem::Label(&lab));
                let res = self.pp_ty(t, true);
                self.state.pop_state(old, StateElem::Label(&lab));
                res
            })
            .collect();
        let doc = concat(doc.into_iter(), ",");
        enclose("(", doc, ")")
    }
    fn pp_ty_func<'b>(&mut self, f: &'b Function) -> RcDoc<'b> {
        let lab = StateElem::TypeStr("func");
        let old = self.state.push_state(&lab);
        let args = self.pp_args(&f.args, "arg");
        let rets = self.pp_args(&f.rets, "ret");
        let modes = candid::pretty::candid::pp_modes(&f.modes);
        let res = args
            .append(" ->")
            .append(RcDoc::space())
            .append(rets.append(modes))
            .nest(INDENT_SPACE);
        self.state.pop_state(old, lab);
        res
    }
    fn pp_ty_service<'b>(&mut self, serv: &'b [(String, Type)]) -> RcDoc<'b> {
        let lab = StateElem::TypeStr("service");
        let old = self.state.push_state(&lab);
        let mut list = Vec::new();
        for (id, func) in serv.iter() {
            let func_doc = match func.as_ref() {
                TypeInner::Func(ref f) => enclose("candid::func!(", self.pp_ty_func(f), ")"),
                TypeInner::Var(_) => self.pp_ty(func, true).append("::ty()"),
                _ => unreachable!(),
            };
            list.push(
                RcDoc::text("\"")
                    .append(id)
                    .append(kwd("\" :"))
                    .append(func_doc),
            );
        }
        let doc = concat(list.into_iter(), ";");
        let res = enclose_space("{", doc, "}");
        self.state.pop_state(old, lab);
        res
    }
    fn pp_function(&mut self, id: &str, func: &Function) -> Method {
        use candid::types::internal::FuncMode;
        let old = self.state.push_state(&StateElem::Label(id));
        let name = self
            .state
            .config
            .name
            .clone()
            .unwrap_or_else(|| ident(id, Some(Case::Snake)).pretty(LINE_WIDTH).to_string());
        let args: Vec<_> = func
            .args
            .iter()
            .enumerate()
            .map(|(i, ty)| {
                let lab = format!("arg{i}");
                let old = self.state.push_state(&StateElem::Label(&lab));
                let name = self
                    .state
                    .config
                    .name
                    .clone()
                    .unwrap_or_else(|| lab.clone());
                let res = self.pp_ty(ty, true);
                self.state.pop_state(old, StateElem::Label(&lab));
                (name, res)
            })
            .collect();
        let rets: Vec<_> = func
            .rets
            .iter()
            .enumerate()
            .map(|(i, ty)| {
                let lab = format!("ret{i}");
                let old = self.state.push_state(&StateElem::Label(&lab));
                let res = self.pp_ty(ty, true);
                self.state.pop_state(old, StateElem::Label(&lab));
                res
            })
            .collect();
        let mode = match func.modes.first() {
            None => "update",
            Some(FuncMode::Query) => "query",
            Some(FuncMode::CompositeQuery) => "composite_query",
            Some(FuncMode::Oneway) => "update",
        }
        .to_string();
        let res = Method {
            name,
            original_name: id.to_string(),
            args: args
                .into_iter()
                .map(|(id, t)| (id, t.pretty(LINE_WIDTH).to_string()))
                .collect(),
            rets: rets
                .into_iter()
                .map(|x| x.pretty(LINE_WIDTH).to_string())
                .collect(),
            mode,
        };
        self.state.pop_state(old, StateElem::Label(id));
        res
    }
    fn pp_actor(&mut self, actor: &Type) -> (Vec<Method>, Option<Vec<(String, String)>>) {
        let actor = self.state.env.trace_type(actor).unwrap();
        let init = if let TypeInner::Class(args, _) = actor.as_ref() {
            let old = self.state.push_state(&StateElem::Label("init"));
            let args: Vec<_> = args
                .iter()
                .enumerate()
                .map(|(i, ty)| {
                    let lab = format!("arg{i}");
                    let old = self.state.push_state(&StateElem::Label(&lab));
                    let name = self
                        .state
                        .config
                        .name
                        .clone()
                        .unwrap_or_else(|| lab.clone());
                    let res = self.pp_ty(ty, true);
                    self.state.pop_state(old, StateElem::Label(&lab));
                    (name, res.pretty(LINE_WIDTH).to_string())
                })
                .collect();
            self.state.pop_state(old, StateElem::Label("init"));
            Some(args)
        } else {
            None
        };
        let serv = self.state.env.as_service(&actor).unwrap();
        let mut res = Vec::new();
        for (id, func) in serv.iter() {
            let func = self.state.env.as_func(func).unwrap();
            res.push(self.pp_function(id, func));
        }
        (res, init)
    }
}
#[derive(Serialize, Debug)]
pub struct Output {
    type_defs: String,
    methods: Vec<Method>,
    init_args: Option<Vec<(String, String)>>,
}
#[derive(Serialize, Debug)]
pub struct Method {
    name: String,
    original_name: String,
    args: Vec<(String, String)>,
    rets: Vec<String>,
    mode: String,
}
pub fn emit_bindgen(tree: &Config, env: &TypeEnv, actor: &Option<Type>) -> (Output, Vec<String>) {
    let (env, actor) = nominalize_all(env, actor);
    let def_list: Vec<_> = if let Some(actor) = &actor {
        chase_actor(&env, actor).unwrap()
    } else {
        env.0.iter().map(|pair| pair.0.as_ref()).collect()
    };
    let recs = infer_rec(&env, &def_list).unwrap();
    let mut state = State {
        state: crate::configs::State::new(&tree.0, &env),
        recs,
    };
    let defs = state.pp_defs(&def_list);
    let (methods, init_args) = if let Some(actor) = &actor {
        state.pp_actor(actor)
    } else {
        (Vec::new(), None)
    };
    let unused = state.state.report_unused();
    (
        Output {
            type_defs: defs.pretty(LINE_WIDTH).to_string(),
            methods,
            init_args,
        },
        unused,
    )
}
pub fn output_handlebar(output: Output, config: ExternalConfig, template: &str) -> String {
    let hbs = get_hbs();
    #[derive(Serialize)]
    struct HBOutput {
        #[serde(flatten)]
        external: BTreeMap<String, String>,
        type_defs: String,
        methods: Vec<Method>,
        init_args: Option<Vec<(String, String)>>,
    }
    let data = HBOutput {
        type_defs: output.type_defs,
        methods: output.methods,
        external: config.0,
        init_args: output.init_args,
    };
    hbs.render_template(template, &data).unwrap()
}
pub struct Config(ConfigTree<BindingConfig>);
impl Config {
    pub fn new(configs: Configs) -> Self {
        Self(ConfigTree::from_configs("rust", configs).unwrap())
    }
}
#[derive(Deserialize)]
pub struct ExternalConfig(pub BTreeMap<String, String>);
impl Default for ExternalConfig {
    fn default() -> Self {
        Self(
            [
                ("candid_crate", "candid"),
                ("service_name", "service"),
                ("target", "canister_call"),
            ]
            .into_iter()
            .map(|(k, v)| (k.to_string(), v.to_string()))
            .collect(),
        )
    }
}
pub fn compile(
    tree: &Config,
    env: &TypeEnv,
    actor: &Option<Type>,
    external: ExternalConfig,
) -> String {
    let source = match external.0.get("target").map(|s| s.as_str()) {
        Some("canister_call") | None => include_str!("rust_call.hbs"),
        Some("agent") => include_str!("rust_agent.hbs"),
        Some("stub") => include_str!("rust_stub.hbs"),
        _ => unimplemented!(),
    };
    let (output, unused) = emit_bindgen(tree, env, actor);
    for e in unused {
        eprintln!("WARNING: path {e} is unused");
    }
    output_handlebar(output, external, source)
}

pub enum TypePath {
    Id(String),
    Opt,
    Vec,
    RecordField(String),
    VariantField(String),
    Func(String),
    Init,
}
fn path_to_var(path: &[TypePath]) -> String {
    let name: Vec<&str> = path
        .iter()
        .map(|node| match node {
            TypePath::Id(id) => id.as_str(),
            TypePath::RecordField(f) | TypePath::VariantField(f) => f.as_str(),
            TypePath::Opt => "inner",
            TypePath::Vec => "item",
            TypePath::Func(id) => id.as_str(),
            TypePath::Init => "init",
        })
        .collect();
    name.join("_").to_case(Case::Pascal)
}
// Convert structural typing to nominal typing to fit Rust's type system
fn nominalize(env: &mut TypeEnv, path: &mut Vec<TypePath>, t: &Type) -> Type {
    match t.as_ref() {
        TypeInner::Opt(ty) => {
            path.push(TypePath::Opt);
            let ty = nominalize(env, path, ty);
            path.pop();
            TypeInner::Opt(ty)
        }
        TypeInner::Vec(ty) => {
            path.push(TypePath::Vec);
            let ty = nominalize(env, path, ty);
            path.pop();
            TypeInner::Vec(ty)
        }
        TypeInner::Record(fs) => {
            if matches!(
                path.last(),
                None | Some(TypePath::VariantField(_)) | Some(TypePath::Id(_))
            ) || is_tuple(fs)
            {
                let fs: Vec<_> = fs
                    .iter()
                    .map(|Field { id, ty }| {
                        path.push(TypePath::RecordField(id.to_string()));
                        let ty = nominalize(env, path, ty);
                        path.pop();
                        Field { id: id.clone(), ty }
                    })
                    .collect();
                TypeInner::Record(fs)
            } else {
                let new_var = path_to_var(path);
                let ty = nominalize(
                    env,
                    &mut vec![TypePath::Id(new_var.clone())],
                    &TypeInner::Record(fs.to_vec()).into(),
                );
                env.0.insert(new_var.clone(), ty);
                TypeInner::Var(new_var)
            }
        }
        TypeInner::Variant(fs) => match path.last() {
            None | Some(TypePath::Id(_)) => {
                let fs: Vec<_> = fs
                    .iter()
                    .map(|Field { id, ty }| {
                        path.push(TypePath::VariantField(id.to_string()));
                        let ty = nominalize(env, path, ty);
                        path.pop();
                        Field { id: id.clone(), ty }
                    })
                    .collect();
                TypeInner::Variant(fs)
            }
            Some(_) => {
                let new_var = path_to_var(path);
                let ty = nominalize(
                    env,
                    &mut vec![TypePath::Id(new_var.clone())],
                    &TypeInner::Variant(fs.to_vec()).into(),
                );
                env.0.insert(new_var.clone(), ty);
                TypeInner::Var(new_var)
            }
        },
        TypeInner::Func(func) => match path.last() {
            None | Some(TypePath::Id(_)) => {
                let func = func.clone();
                TypeInner::Func(Function {
                    modes: func.modes,
                    args: func
                        .args
                        .into_iter()
                        .enumerate()
                        .map(|(i, ty)| {
                            let i = if i == 0 {
                                "".to_string()
                            } else {
                                i.to_string()
                            };
                            path.push(TypePath::Func(format!("arg{i}")));
                            let ty = nominalize(env, path, &ty);
                            path.pop();
                            ty
                        })
                        .collect(),
                    rets: func
                        .rets
                        .into_iter()
                        .enumerate()
                        .map(|(i, ty)| {
                            let i = if i == 0 {
                                "".to_string()
                            } else {
                                i.to_string()
                            };
                            path.push(TypePath::Func(format!("ret{i}")));
                            let ty = nominalize(env, path, &ty);
                            path.pop();
                            ty
                        })
                        .collect(),
                })
            }
            Some(_) => {
                let new_var = path_to_var(path);
                let ty = nominalize(
                    env,
                    &mut vec![TypePath::Id(new_var.clone())],
                    &TypeInner::Func(func.clone()).into(),
                );
                env.0.insert(new_var.clone(), ty);
                TypeInner::Var(new_var)
            }
        },
        TypeInner::Service(serv) => match path.last() {
            None | Some(TypePath::Id(_)) => TypeInner::Service(
                serv.iter()
                    .map(|(meth, ty)| {
                        path.push(TypePath::Id(meth.to_string()));
                        let ty = nominalize(env, path, ty);
                        path.pop();
                        (meth.clone(), ty)
                    })
                    .collect(),
            ),
            Some(_) => {
                let new_var = path_to_var(path);
                let ty = nominalize(
                    env,
                    &mut vec![TypePath::Id(new_var.clone())],
                    &TypeInner::Service(serv.clone()).into(),
                );
                env.0.insert(new_var.clone(), ty);
                TypeInner::Var(new_var)
            }
        },
        TypeInner::Class(args, ty) => TypeInner::Class(
            args.iter()
                .map(|ty| {
                    path.push(TypePath::Init);
                    let ty = nominalize(env, path, ty);
                    path.pop();
                    ty
                })
                .collect(),
            nominalize(env, path, ty),
        ),
        _ => return t.clone(),
    }
    .into()
}

fn nominalize_all(env: &TypeEnv, actor: &Option<Type>) -> (TypeEnv, Option<Type>) {
    let mut res = TypeEnv(Default::default());
    for (id, ty) in env.0.iter() {
        let ty = nominalize(&mut res, &mut vec![TypePath::Id(id.clone())], ty);
        res.0.insert(id.to_string(), ty);
    }
    let actor = actor
        .as_ref()
        .map(|ty| nominalize(&mut res, &mut vec![], ty));
    (res, actor)
}
pub fn check_rust(source: &str, candid: &Output) {
    use codespan_reporting::{
        files::SimpleFile,
        term::{self, termcolor::StandardStream},
    };
    let rust = get_endpoint_from_rust_source(source);
    let diags = diff_did_and_rust(candid, &rust);
    let writer = StandardStream::stderr(term::termcolor::ColorChoice::Auto);
    let config = term::Config::default();
    let file = SimpleFile::new("rust code", source);
    for diag in diags {
        term::emit(&mut writer.lock(), &config, &file, &diag).unwrap();
    }
}
fn get_endpoint_from_rust_source(source: &str) -> Vec<CDKMethod> {
    use syn::visit::{self, Visit};
    use syn::{ImplItemFn, ItemFn};
    struct FnVisitor(Vec<CDKMethod>);
    impl<'ast> Visit<'ast> for FnVisitor {
        fn visit_item_fn(&mut self, node: &'ast ItemFn) {
            if let Some(m) = get_cdk_function(&node.attrs, &node.sig) {
                self.0.push(m);
            }
            // handle nested functions
            visit::visit_item_fn(self, node);
        }
        fn visit_impl_item_fn(&mut self, node: &'ast ImplItemFn) {
            if let Some(m) = get_cdk_function(&node.attrs, &node.sig) {
                self.0.push(m);
            }
            // handle nested functions
            visit::visit_impl_item_fn(self, node);
        }
    }
    let ast = syn::parse_file(source).unwrap();
    let mut visitor = FnVisitor(Vec::new());
    visitor.visit_file(&ast);
    for m in &visitor.0 {
        m.debug_print(source);
    }
    visitor.0
}
struct CDKMethod {
    func_name: syn::Ident,
    export_name: Option<(String, syn::Meta)>,
    composite: Option<syn::Meta>,
    mode: syn::Ident,
    args: Vec<syn::Type>,
    rets: Vec<syn::Type>,
}
impl CDKMethod {
    fn debug_print(&self, source: &str) {
        use syn::spanned::Spanned;
        println!("{} {}", self.func_name, self.mode);
        if let Some((_, meta)) = &self.export_name {
            let range = meta.span().byte_range();
            println!(" export {}", &source[range]);
        }
        if let Some(composite) = &self.composite {
            let range = composite.span().byte_range();
            println!(" composite {}", &source[range]);
        }
        for arg in &self.args {
            let range = arg.span().byte_range();
            println!(" arg {}", &source[range]);
        }
        for ret in &self.rets {
            let range = ret.span().byte_range();
            println!(" ret {}", &source[range]);
        }
    }
}
use codespan_reporting::diagnostic::Diagnostic;
fn diff_did_and_rust(candid: &Output, rust: &[CDKMethod]) -> Vec<Diagnostic<()>> {
    use codespan_reporting::diagnostic::Label;
    use syn::spanned::Spanned;
    let mut res = Vec::new();
    let rust: BTreeMap<_, _> = rust
        .iter()
        .map(|m| {
            let name = m
                .export_name
                .as_ref()
                .map(|x| x.0.clone())
                .unwrap_or(m.func_name.to_string());
            (name, m)
        })
        .collect();
    for m in &candid.methods {
        let diag = Diagnostic::error()
            .with_message(format!("Error with Candid method {}", m.original_name));
        let mut labels = Vec::new();
        let mut notes = Vec::new();
        if let Some(func) = rust.get(&m.original_name) {
            if m.original_name == m.name {
            } else {
                if let Some((name, meta)) = &func.export_name {
                    if *name != m.original_name {
                        labels
                            .push(Label::primary((), meta.span().byte_range()).with_message(
                                format!("expect {}", m.original_name.escape_debug()),
                            ));
                    }
                } else {
                    labels.push(
                        Label::primary((), func.mode.span().byte_range()).with_message(format!(
                            "missing (name = \"{}\")",
                            m.original_name.escape_debug()
                        )),
                    );
                }
            }
            let args = func.args.iter().zip(m.args.iter().map(|x| &x.1));
            for (rust_arg, candid_arg) in args {
                let parsed_candid_arg: syn::Type = syn::parse_str(candid_arg).unwrap();
                if parsed_candid_arg != *rust_arg {
                    labels.push(
                        Label::primary((), rust_arg.span().byte_range())
                            .with_message(format!("expect type: {}", candid_arg)),
                    );
                }
            }
        } else {
            notes.push(format!(
                "method \"{}\" missing from Rust code",
                m.original_name
            ));
        }
        res.push(diag.with_labels(labels).with_notes(notes));
    }
    res
}
fn get_cdk_function(attrs: &[syn::Attribute], sig: &syn::Signature) -> Option<CDKMethod> {
    use syn::parse::Parser;
    use syn::{Expr, ExprLit, FnArg, Lit, Meta, ReturnType};
    let func_name = sig.ident.clone();
    let mut mode = None;
    let mut export_name = None;
    let mut composite = None;
    for attr in attrs {
        let attr_name = &attr.meta.path().segments.last().unwrap().ident;
        if attr_name != "update" && attr_name != "query" && attr_name != "init" {
            continue;
        }
        mode = Some(attr_name.clone());
        if let Meta::List(list) = &attr.meta {
            let nested = syn::punctuated::Punctuated::<Meta, syn::Token![,]>::parse_terminated
                .parse2(list.tokens.clone())
                .unwrap();
            for meta in nested {
                if let Meta::NameValue(ref m) = meta {
                    if m.path.is_ident("name") {
                        if let Expr::Lit(ExprLit {
                            lit: Lit::Str(name),
                            ..
                        }) = &m.value
                        {
                            export_name = Some((name.value(), meta));
                        }
                    } else if m.path.is_ident("composite") {
                        if let Expr::Lit(ExprLit {
                            lit: Lit::Bool(b), ..
                        }) = &m.value
                        {
                            if b.value {
                                composite = Some(meta);
                            }
                        }
                    }
                }
            }
        }
    }
    let args = sig
        .inputs
        .iter()
        .filter_map(|arg| match arg {
            FnArg::Receiver(_) => None,
            FnArg::Typed(pat) => Some(*pat.ty.clone()),
        })
        .collect();
    let rets = match &sig.output {
        ReturnType::Default => Vec::new(),
        ReturnType::Type(_, ty) => match ty.as_ref() {
            syn::Type::Tuple(ty) => ty.elems.iter().map(|t| (*t).clone()).collect(),
            _ => vec![*ty.clone()],
        },
    };
    mode.map(|mode| CDKMethod {
        func_name,
        export_name,
        composite,
        args,
        rets,
        mode,
    })
}
fn get_hbs() -> handlebars::Handlebars<'static> {
    use handlebars::*;
    let mut hbs = Handlebars::new();
    hbs.register_escape_fn(handlebars::no_escape);
    hbs.set_strict_mode(true);
    hbs.register_helper(
        "escape_debug",
        Box::new(
            |h: &Helper,
             _: &Handlebars,
             _: &Context,
             _: &mut RenderContext,
             out: &mut dyn Output|
             -> HelperResult {
                let s = h.param(0).unwrap().value().as_str().unwrap();
                out.write(&s.escape_debug().to_string())?;
                Ok(())
            },
        ),
    );
    hbs.register_helper(
        "snake_case",
        Box::new(
            |h: &Helper,
             _: &Handlebars,
             _: &Context,
             _: &mut RenderContext,
             out: &mut dyn Output|
             -> HelperResult {
                let s = h.param(0).unwrap().value().as_str().unwrap();
                out.write(s.to_case(Case::Snake).as_ref())?;
                Ok(())
            },
        ),
    );
    hbs.register_helper(
        "PascalCase",
        Box::new(
            |h: &Helper,
             _: &Handlebars,
             _: &Context,
             _: &mut RenderContext,
             out: &mut dyn Output|
             -> HelperResult {
                let s = h.param(0).unwrap().value().as_str().unwrap();
                out.write(s.to_case(Case::Pascal).as_ref())?;
                Ok(())
            },
        ),
    );
    hbs.register_helper(
        "vec_to_arity",
        Box::new(
            |h: &Helper,
             _: &Handlebars,
             _: &Context,
             _: &mut RenderContext,
             out: &mut dyn Output|
             -> HelperResult {
                let vec: Vec<_> = h
                    .param(0)
                    .unwrap()
                    .value()
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|v| v.as_str().unwrap())
                    .collect();
                match vec.len() {
                    1 => out.write(vec[0])?,
                    _ => out.write(&format!("({})", vec.join(", ")))?,
                }
                Ok(())
            },
        ),
    );
    hbs.register_helper(
        "principal_slice",
        Box::new(
            |h: &Helper,
             _: &Handlebars,
             _: &Context,
             _: &mut RenderContext,
             out: &mut dyn Output|
             -> HelperResult {
                let s = h.param(0).unwrap().value().as_str().unwrap();
                let id = crate::Principal::from_text(s).unwrap();
                let slice = id
                    .as_slice()
                    .iter()
                    .map(|b| b.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                out.write(slice.as_str())?;
                Ok(())
            },
        ),
    );
    hbs.register_helper(
        "cdk_attribute",
        Box::new(
            |h: &Helper,
             _: &Handlebars,
             _: &Context,
             _: &mut RenderContext,
             out: &mut dyn Output|
             -> HelperResult {
                let mode = h.param(0).unwrap().value().as_str().unwrap();
                let name = h.param(1).unwrap().value().as_str().unwrap();
                let original_name = h.param(2).unwrap().value().as_str().unwrap();
                if mode == "update" {
                    out.write("update")?;
                } else {
                    out.write("query")?;
                }
                let mut attrs = Vec::new();
                if mode == "composite_query" {
                    attrs.push("composite = true".to_string());
                }
                if name != original_name {
                    attrs.push(format!("name = \"{}\"", original_name.escape_debug()));
                }
                let attrs = attrs.join(", ");
                if !attrs.is_empty() {
                    out.write(&format!("({attrs})"))?;
                }
                Ok(())
            },
        ),
    );
    hbs
}
