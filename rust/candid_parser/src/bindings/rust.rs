use super::analysis::{chase_actor, infer_rec};
use crate::{
    configs::{ConfigState, ConfigTree, Configs, StateElem},
    Deserialize,
};
use candid::pretty::utils::*;
use candid::types::{Field, Function, Label, SharedLabel, Type, TypeEnv, TypeInner};
use convert_case::{Case, Casing};
use pretty::RcDoc;
use std::collections::BTreeSet;

#[derive(Clone)]
pub enum Target {
    CanisterCall,
    Agent,
    CanisterStub,
}

//#[derive(Clone)]
pub struct Config {
    candid_crate: String,
    tree: ConfigTree<BindingConfig>,
    canister_id: Option<candid::Principal>,
    service_name: String,
    target: Target,
}
impl Config {
    pub fn new(configs: Configs) -> Self {
        let tree = ConfigTree::from_configs("rust", configs).unwrap();
        Config {
            candid_crate: "candid".to_string(),
            tree,
            canister_id: None,
            service_name: "service".to_string(),
            target: Target::CanisterCall,
        }
    }
    pub fn set_candid_crate(&mut self, name: String) -> &mut Self {
        self.candid_crate = name;
        self
    }
    /// Only generates SERVICE struct if canister_id is not provided
    pub fn set_canister_id(&mut self, id: candid::Principal) -> &mut Self {
        self.canister_id = Some(id);
        self
    }
    /// Service name when canister id is provided
    pub fn set_service_name(&mut self, name: String) -> &mut Self {
        self.service_name = name;
        self
    }
    pub fn set_target(&mut self, name: Target) -> &mut Self {
        self.target = name;
        self
    }
}
#[derive(Default, Deserialize, Clone)]
pub struct BindingConfig {
    name: Option<String>,
    use_type: Option<String>,
    attributes: Option<String>,
    visibility: Option<String>,
}
impl ConfigState for BindingConfig {
    fn merge_config(&mut self, config: &Self, _is_recursive: bool) {
        self.name = config.name.clone();
        self.use_type = config.use_type.clone();
        self.attributes = config.attributes.clone();
        if config.visibility.is_some() {
            self.visibility = config.visibility.clone();
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

impl<'a> State<'a> {
    fn pp_ty<'b>(&mut self, ty: &'b Type, is_ref: bool) -> RcDoc<'b> {
        use TypeInner::*;
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
                let name = ident(id, Some(Case::Pascal));
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
            Record(ref fs) => self.pp_record_fields(fs, false),
            Variant(_) => unreachable!(), // not possible after rewriting
            Func(_) => unreachable!(),    // not possible after rewriting
            Service(_) => unreachable!(), // not possible after rewriting
            Class(_, _) => unreachable!(),
            Knot(_) | Unknown | Future => unreachable!(),
        }
    }
    fn pp_label<'b>(&mut self, id: &'b SharedLabel, is_variant: bool, need_vis: bool) -> RcDoc<'b> {
        let label = id.to_string();
        let old = self.state.push_state(&StateElem::Label(&label));
        let vis = if need_vis {
            RcDoc::text(
                self.state
                    .config
                    .visibility
                    .clone()
                    .unwrap_or("pub".to_string()),
            )
            .append(" ")
        } else {
            RcDoc::nil()
        };
        let res = match &**id {
            Label::Named(id) => {
                let case = if is_variant { Some(Case::Pascal) } else { None };
                let (doc, is_rename) = ident_(id, case);
                if is_rename {
                    str("#[serde(rename=\"")
                        .append(id.escape_debug().to_string())
                        .append("\")]")
                        .append(RcDoc::line())
                        .append(vis)
                        .append(doc)
                } else {
                    vis.append(doc)
                }
            }
            Label::Id(n) | Label::Unnamed(n) => {
                vis.append("_").append(RcDoc::as_string(n)).append("_")
            }
        };
        self.state.pop_state(old, StateElem::Label(&label));
        res
    }
    fn pp_tuple<'b>(&mut self, fs: &'b [Field], need_vis: bool) -> RcDoc<'b> {
        let tuple = fs.iter().enumerate().map(|(i, f)| {
            let lab = i.to_string();
            let old = self.state.push_state(&StateElem::Label(&lab));
            let vis = if need_vis {
                RcDoc::text(
                    self.state
                        .config
                        .visibility
                        .clone()
                        .unwrap_or("pub".to_string()),
                )
                .append(" ")
            } else {
                RcDoc::nil()
            };
            let res = vis.append(self.pp_ty(&f.ty, false)).append(",");
            self.state.pop_state(old, StateElem::Label(&lab));
            res
        });
        enclose("(", RcDoc::concat(tuple), ")")
    }
    fn pp_record_field<'b>(&mut self, field: &'b Field, need_vis: bool) -> RcDoc<'b> {
        self.pp_label(&field.id, false, need_vis)
            .append(kwd(":"))
            .append(self.pp_ty(&field.ty, false))
    }
    fn pp_record_fields<'b>(&mut self, fs: &'b [Field], need_vis: bool) -> RcDoc<'b> {
        let old = self.state.push_state(&StateElem::Label("record"));
        let res = if is_tuple(fs) {
            self.pp_tuple(fs, need_vis)
        } else {
            let fields: Vec<_> = fs
                .iter()
                .map(|f| self.pp_record_field(f, need_vis))
                .collect();
            let fields = concat(fields.into_iter(), ",");
            enclose_space("{", fields, "}")
        };
        self.state.pop_state(old, StateElem::Label("record"));
        res
    }
    fn pp_variant_field<'b>(&mut self, field: &'b Field) -> RcDoc<'b> {
        match field.ty.as_ref() {
            TypeInner::Null => self.pp_label(&field.id, true, false),
            TypeInner::Record(fs) => self
                .pp_label(&field.id, true, false)
                .append(self.pp_record_fields(fs, false)),
            _ => self.pp_label(&field.id, true, false).append(enclose(
                "(",
                self.pp_ty(&field.ty, false),
                ")",
            )),
        }
    }

    fn pp_variant_fields<'b>(&mut self, fs: &'b [Field]) -> RcDoc<'b> {
        let old = self.state.push_state(&StateElem::Label("variant"));
        let fields: Vec<_> = fs.iter().map(|f| self.pp_variant_field(f)).collect();
        let fields = concat(fields.into_iter(), ",");
        let res = enclose_space("{", fields, "}");
        self.state.pop_state(old, StateElem::Label("variant"));
        res
    }
    fn pp_defs(&mut self, def_list: &'a [&'a str]) -> RcDoc<'a> {
        lines(def_list.iter().map(|id| {
            let old = self.state.push_state(&StateElem::Label(id));
            let ty = self.state.env.find_type(id).unwrap();
            let name = self
                .state
                .config
                .name
                .clone()
                .map(RcDoc::text)
                .unwrap_or_else(|| ident(id, Some(Case::Pascal)).append(" "));
            let vis = self
                .state
                .config
                .visibility
                .clone()
                .map(|v| RcDoc::text(v).append(" "))
                .unwrap_or(RcDoc::text("pub "));
            let derive = self
                .state
                .config
                .attributes
                .clone()
                .map(RcDoc::text)
                .unwrap_or(RcDoc::text("#[derive(CandidType, Deserialize)]"));
            let res = match ty.as_ref() {
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
                        .append(self.pp_record_fields(fs, true))
                        .append(separator)
                        .append(RcDoc::hardline())
                }
                TypeInner::Variant(fs) => derive
                    .append(RcDoc::line())
                    .append(vis)
                    .append("enum ")
                    .append(name)
                    .append(self.pp_variant_fields(fs))
                    .append(RcDoc::hardline()),
                TypeInner::Func(func) => str("candid::define_function!(")
                    .append(vis)
                    .append(name)
                    .append(": ")
                    .append(self.pp_ty_func(func))
                    .append(");"),
                TypeInner::Service(serv) => str("candid::define_service!(")
                    .append(vis)
                    .append(name)
                    .append(": ")
                    .append(self.pp_ty_service(serv))
                    .append(");"),
                _ => {
                    if self.recs.contains(id) {
                        derive
                            .append(RcDoc::line())
                            .append(vis)
                            .append("struct ")
                            .append(ident(id, Some(Case::Pascal)))
                            .append(enclose("(", self.pp_ty(ty, false), ")"))
                            .append(";")
                            .append(RcDoc::hardline())
                    } else {
                        vis.append(kwd("type"))
                            .append(name)
                            .append("= ")
                            .append(self.pp_ty(ty, false))
                            .append(";")
                    }
                }
            };
            self.state.pop_state(old, StateElem::Label(id));
            res
        }))
    }
    fn pp_args<'b>(&mut self, args: &'b [Type]) -> RcDoc<'b> {
        let doc: Vec<_> = args.iter().map(|t| self.pp_ty(t, true)).collect();
        let doc = concat(doc.into_iter(), ",");
        enclose("(", doc, ")")
    }
    fn pp_ty_func<'b>(&mut self, f: &'b Function) -> RcDoc<'b> {
        let args = self.pp_args(&f.args);
        let rets = self.pp_args(&f.rets);
        let modes = candid::pretty::candid::pp_modes(&f.modes);
        args.append(" ->")
            .append(RcDoc::space())
            .append(rets.append(modes))
            .nest(INDENT_SPACE)
    }
    fn pp_ty_service<'b>(&mut self, serv: &'b [(String, Type)]) -> RcDoc<'b> {
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
        enclose_space("{", doc, "}")
    }
}

fn pp_function<'a>(config: &'a Config, id: &'a str, func: &'a Function) -> RcDoc<'a> {
    let env = TypeEnv::default();
    let mut state = State {
        state: crate::configs::State::new(&config.tree, &env),
        recs: RecPoints::default(),
    };
    let name = ident(id, Some(Case::Snake));
    let arg_prefix = str(match config.target {
        Target::CanisterCall => "&self",
        Target::Agent => "&self",
        Target::CanisterStub => unimplemented!(),
    });
    let args: Vec<_> = func
        .args
        .iter()
        .enumerate()
        .map(|(i, ty)| RcDoc::as_string(format!("arg{i}: ")).append(state.pp_ty(ty, true)))
        .collect();
    let args = concat(std::iter::once(arg_prefix).chain(args), ",");
    let rets: Vec<_> = func
        .rets
        .iter()
        .map(|ty| state.pp_ty(ty, true).append(","))
        .collect();
    let rets = match config.target {
        Target::CanisterCall => enclose("(", RcDoc::concat(rets), ")"),
        Target::Agent => match func.rets.len() {
            0 => str("()"),
            1 => state.pp_ty(&func.rets[0], true),
            _ => enclose(
                "(",
                RcDoc::intersperse(
                    func.rets.iter().map(|ty| state.pp_ty(ty, true)),
                    RcDoc::text(", "),
                ),
                ")",
            ),
        },
        Target::CanisterStub => unimplemented!(),
    };
    let sig = kwd("pub async fn")
        .append(name)
        .append(enclose("(", args, ")"))
        .append(kwd(" ->"))
        .append(enclose("Result<", rets, "> "));
    let method = id.escape_debug().to_string();
    let body = match config.target {
        Target::CanisterCall => {
            let args = RcDoc::concat((0..func.args.len()).map(|i| RcDoc::text(format!("arg{i},"))));
            str("ic_cdk::call(self.0, \"")
                .append(method)
                .append("\", ")
                .append(enclose("(", args, ")"))
                .append(").await")
        }
        Target::Agent => {
            let is_query = func.is_query();
            let builder_method = if is_query { "query" } else { "update" };
            let call = if is_query { "call" } else { "call_and_wait" };
            let args = RcDoc::intersperse(
                (0..func.args.len()).map(|i| RcDoc::text(format!("&arg{i}"))),
                RcDoc::text(", "),
            );
            let blob = str("Encode!").append(enclose("(", args, ")?;"));
            let rets = RcDoc::concat(
                func.rets
                    .iter()
                    .map(|ty| str(", ").append(state.pp_ty(ty, true))),
            );
            str("let args = ").append(blob).append(RcDoc::hardline())
                .append(format!("let bytes = self.1.{builder_method}(&self.0, \"{method}\").with_arg(args).{call}().await?;"))
                .append(RcDoc::hardline())
                .append("Ok(Decode!(&bytes").append(rets).append(")?)")
        }
        Target::CanisterStub => unimplemented!(),
    };
    sig.append(enclose_space("{", body, "}"))
}

fn pp_actor<'a>(config: &'a Config, env: &'a TypeEnv, actor: &'a Type) -> RcDoc<'a> {
    // TODO trace to service before we figure out what canister means in Rust
    let serv = env.as_service(actor).unwrap();
    let body = RcDoc::intersperse(
        serv.iter().map(|(id, func)| {
            let func = env.as_func(func).unwrap();
            pp_function(config, id, func)
        }),
        RcDoc::hardline(),
    );
    let struct_name = config.service_name.to_case(Case::Pascal);
    let service_def = match config.target {
        Target::CanisterCall => format!("pub struct {}(pub Principal);", struct_name),
        Target::Agent => format!(
            "pub struct {}<'a>(pub Principal, pub &'a ic_agent::Agent);",
            struct_name
        ),
        Target::CanisterStub => unimplemented!(),
    };
    let service_impl = match config.target {
        Target::CanisterCall => format!("impl {} ", struct_name),
        Target::Agent => format!("impl<'a> {}<'a> ", struct_name),
        Target::CanisterStub => unimplemented!(),
    };
    let res = RcDoc::text(service_def)
        .append(RcDoc::hardline())
        .append(service_impl)
        .append(enclose_space("{", body, "}"))
        .append(RcDoc::hardline());
    if let Some(cid) = config.canister_id {
        let slice = cid
            .as_slice()
            .iter()
            .map(|b| b.to_string())
            .collect::<Vec<_>>()
            .join(", ");
        let id = RcDoc::text(format!(
            "pub const CANISTER_ID : Principal = Principal::from_slice(&[{}]); // {}",
            slice, cid
        ));
        let instance = match config.target {
            Target::CanisterCall => format!(
                "pub const {} : {} = {}(CANISTER_ID);",
                config.service_name, struct_name, struct_name
            ),
            Target::Agent => "".to_string(),
            Target::CanisterStub => unimplemented!(),
        };
        res.append(id).append(RcDoc::hardline()).append(instance)
    } else {
        res
    }
}

pub fn compile(config: &Config, env: &TypeEnv, actor: &Option<Type>) -> String {
    let header = format!(
        r#"// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
#![allow(dead_code, unused_imports)]
use {}::{{self, CandidType, Deserialize, Principal, Encode, Decode}};
"#,
        config.candid_crate
    );
    let header = header
        + match &config.target {
            Target::CanisterCall => "use ic_cdk::api::call::CallResult as Result;\n",
            Target::Agent => "type Result<T> = std::result::Result<T, ic_agent::AgentError>;\n",
            Target::CanisterStub => "",
        };
    let (env, actor) = nominalize_all(env, actor);
    let def_list: Vec<_> = if let Some(actor) = &actor {
        chase_actor(&env, actor).unwrap()
    } else {
        env.0.iter().map(|pair| pair.0.as_ref()).collect()
    };
    let recs = infer_rec(&env, &def_list).unwrap();
    let mut state = State {
        state: crate::configs::State::new(&config.tree, &env),
        recs,
    };
    let defs = state.pp_defs(&def_list);
    let doc = match &actor {
        None => defs,
        Some(actor) => {
            let actor = pp_actor(config, &env, actor);
            defs.append(actor)
        }
    };
    let doc = RcDoc::text(header).append(RcDoc::line()).append(doc);
    doc.pretty(LINE_WIDTH).to_string()
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
