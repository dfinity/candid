use super::analysis::{chase_actor, infer_rec};
use crate::{
    configs::{ConfigState, ConfigTree, Configs, Context, StateElem},
    Deserialize,
};
use candid::types::{
    syntax::{self, IDLMergedProg, IDLType},
    Field, Function, Label, SharedLabel, Type, TypeEnv, TypeInner,
};
use candid::{pretty::utils::*, types::ArgType};
use convert_case::{Case, Casing};
use pretty::RcDoc;
use serde::Serialize;
use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};

const DOC_COMMENT_PREFIX: &str = "/// ";

#[derive(Default, Deserialize, Clone, Debug)]
pub struct BindingConfig {
    name: Option<String>,
    use_type: Option<String>,
    attributes: Option<String>,
    visibility: Option<String>,
}
impl ConfigState for BindingConfig {
    fn merge_config(&mut self, config: &Self, ctx: Option<Context>) -> Vec<String> {
        let mut res = Vec::new();
        self.name.clone_from(&config.name);
        res.push("name");
        // match use_type can survive across types, so that label.use_type works
        if ctx
            .as_ref()
            .is_some_and(|ctx| matches!(ctx.elem, StateElem::Type(_) | StateElem::TypeStr(_)))
        {
            if let Some(use_type) = &config.use_type {
                self.use_type = Some(use_type.clone());
                res.push("use_type");
            }
        } else {
            self.use_type.clone_from(&config.use_type);
            res.push("use_type");
        }
        // matched attributes can survive across labels, so that record.attributes works
        if ctx
            .as_ref()
            .is_some_and(|ctx| matches!(ctx.elem, StateElem::Label(_)))
        {
            if let Some(attr) = &config.attributes {
                self.attributes = Some(attr.clone());
                res.push("attributes");
            }
        } else {
            self.attributes.clone_from(&config.attributes);
            res.push("attributes");
        }
        if config.visibility.is_some() {
            self.visibility.clone_from(&config.visibility);
            res.push("visibility");
        }
        res.into_iter().map(|f| f.to_string()).collect()
    }
    fn update_state(&mut self, _elem: &StateElem) {}
    fn restore_state(&mut self, _elem: &StateElem) {}
    fn list_properties(&self) -> Vec<String> {
        let mut res = Vec::new();
        if self.name.is_some() {
            res.push("name");
        }
        if self.use_type.is_some() {
            res.push("use_type");
        }
        if self.attributes.is_some() {
            res.push("attributes");
        }
        if self.visibility.is_some() {
            res.push("visibility");
        }
        res.into_iter().map(|f| f.to_string()).collect()
    }
}
struct State<'a> {
    state: crate::configs::State<'a, BindingConfig>,
    prog: &'a IDLMergedProg,
    recs: RecPoints<'a>,
    tests: BTreeMap<String, String>,
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
fn as_result(fs: &[Field]) -> Option<(&Type, &Type, bool)> {
    match fs {
        [Field { id: ok, ty: t_ok }, Field { id: err, ty: t_err }]
            if **ok == Label::Named("Ok".to_string())
                && **err == Label::Named("Err".to_string()) =>
        {
            Some((t_ok, t_err, false))
        }
        [Field { id: ok, ty: t_ok }, Field { id: err, ty: t_err }]
            if **ok == Label::Named("ok".to_string())
                && **err == Label::Named("err".to_string()) =>
        {
            Some((t_ok, t_err, true))
        }
        _ => None,
    }
}
fn parse_use_type(input: &str) -> (String, bool) {
    if let Some((t, "")) = input.rsplit_once("(no test)") {
        (t.trim_end().to_string(), false)
    } else {
        (input.to_string(), true)
    }
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

fn pp_docs<'a>(docs: &'a [String]) -> RcDoc<'a> {
    lines(
        docs.iter()
            .map(|line| RcDoc::text(DOC_COMMENT_PREFIX).append(line)),
    )
}

fn find_field<'a>(
    fields: Option<&'a [syntax::TypeField]>,
    label: &'a Label,
) -> (RcDoc<'a>, Option<&'a syntax::IDLType>) {
    let mut docs = RcDoc::nil();
    let mut syntax_field_ty = None;
    if let Some(bs) = fields {
        if let Some(field) = bs.iter().find(|b| b.label == *label) {
            docs = pp_docs(&field.docs);
            syntax_field_ty = Some(&field.typ);
        }
    };
    (docs, syntax_field_ty)
}

impl<'a> State<'a> {
    fn generate_test(&mut self, src: &Type, use_type: &str) {
        if self.tests.contains_key(use_type) {
            return;
        }
        let def_list = chase_actor(self.state.env, src).unwrap();
        let env = TypeEnv(
            self.state
                .env
                .0
                .iter()
                .filter(|(k, _)| def_list.contains(&k.as_str()))
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect(),
        );
        let src = candid::pretty::candid::pp_init_args(
            &env,
            &[ArgType {
                name: None,
                typ: src.clone(),
            }],
        )
        .pretty(80)
        .to_string();
        let match_path = self.state.config_source.get("use_type").unwrap().join(".");
        let test_name = use_type.replace(|c: char| !c.is_ascii_alphanumeric(), "_");
        let body = format!(
            r##"#[test]
fn test_{test_name}() {{
  // Generated from {match_path}.use_type = "{use_type}"
  let candid_src = r#"{src}"#;
  candid_parser::utils::check_rust_type::<{use_type}>(candid_src).unwrap();
}}"##
        );
        self.tests.insert(use_type.to_string(), body);
    }

    fn use_type_doc<'b>(&mut self, ty: &'b Type) -> Option<RcDoc<'b>> {
        if let Some(t) = &self.state.config.use_type {
            let (t, need_test) = parse_use_type(t);
            if need_test {
                self.generate_test(ty, &t);
            }
            let res = RcDoc::text(t);
            self.state.update_stats("use_type");
            Some(res)
        } else {
            None
        }
    }

    fn pp_ty_rich<'b>(
        &mut self,
        ty: &'b Type,
        syntax: Option<&'b IDLType>,
        is_ref: bool,
    ) -> RcDoc<'b> {
        let elem = StateElem::Type(ty);
        let old = self.state.push_state(&elem);
        let res = if let Some(use_type_doc) = self.use_type_doc(ty) {
            use_type_doc
        } else {
            match (ty.as_ref(), syntax) {
                (TypeInner::Record(ref fields), Some(IDLType::RecordT(syntax_fields))) => {
                    self.pp_record_fields(fields, Some(syntax_fields), false, is_ref)
                }
                (TypeInner::Variant(ref fields), Some(IDLType::VariantT(syntax_fields))) => {
                    self.pp_variant(fields, Some(syntax_fields), is_ref)
                }
                (_, _) => self.pp_ty(ty, is_ref),
            }
        };
        self.state.pop_state(old, elem);
        res
    }

    fn pp_ty<'b>(&mut self, ty: &'b Type, is_ref: bool) -> RcDoc<'b> {
        use TypeInner::*;
        let elem = StateElem::Type(ty);
        let old = self.state.push_state(&elem);
        let res = if let Some(use_type_doc) = self.use_type_doc(ty) {
            use_type_doc
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
                Var(ref id) => self.pp_var(id, is_ref),
                Principal => str("Principal"),
                Opt(ref t) => self.pp_opt(t, is_ref),
                // It's a bit tricky to use `deserialize_with = "serde_bytes"`. It's not working for `type t = blob`
                Vec(ref t) if matches!(t.as_ref(), Nat8) => str("serde_bytes::ByteBuf"),
                Vec(ref t) => self.pp_vec(t, is_ref),
                Record(ref fs) => self.pp_record_fields(fs, None, false, is_ref),
                Variant(ref fs) => self.pp_variant(fs, None, is_ref),
                Func(_) => unreachable!(), // not possible after rewriting
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
            self.state.update_stats("visibility");
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
        self.state.update_stats("attributes");
        match &**id {
            Label::Named(id) => {
                let (doc, is_rename) = if let Some(name) = &self.state.config.name {
                    let res = (RcDoc::text(name.clone()), true);
                    self.state.update_stats("name");
                    res
                } else {
                    let case = if is_variant {
                        Some(Case::Pascal)
                    } else if !id.starts_with('_') {
                        Some(Case::Snake)
                    } else {
                        None
                    };
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

    fn pp_var<'b>(&mut self, id: &'b str, is_ref: bool) -> RcDoc<'b> {
        let name = if let Some(name) = &self.state.config.name {
            let res = RcDoc::text(name.clone());
            self.state.update_stats("name");
            res
        } else {
            ident(id, Some(Case::Pascal))
        };
        if !is_ref && self.recs.contains(id) {
            str("Box<").append(name).append(">")
        } else {
            name
        }
    }

    fn pp_vec<'b>(&mut self, ty: &'b Type, is_ref: bool) -> RcDoc<'b> {
        str("Vec").append(enclose("<", self.pp_ty(ty, is_ref), ">"))
    }

    fn pp_opt<'b>(&mut self, ty: &'b Type, is_ref: bool) -> RcDoc<'b> {
        str("Option").append(enclose("<", self.pp_ty(ty, is_ref), ">"))
    }

    fn pp_tuple<'b>(&mut self, fs: &'b [Field], need_vis: bool, is_ref: bool) -> RcDoc<'b> {
        let tuple = fs.iter().enumerate().map(|(i, f)| {
            let lab = i.to_string();
            let old = self.state.push_state(&StateElem::Label(&lab));
            let vis = if need_vis {
                self.state.update_stats("visibility");
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

    fn pp_record_field<'b>(
        &mut self,
        field: &'b Field,
        syntax: Option<&'b IDLType>,
        need_vis: bool,
        is_ref: bool,
    ) -> RcDoc<'b> {
        let lab = field.id.to_string();
        let old = self.state.push_state(&StateElem::Label(&lab));
        let res = self
            .pp_label(&field.id, false, need_vis)
            .append(kwd(":"))
            .append(self.pp_ty_rich(&field.ty, syntax, is_ref));
        self.state.pop_state(old, StateElem::Label(&lab));
        res
    }

    fn pp_record_fields<'b>(
        &mut self,
        fs: &'b [Field],
        syntax: Option<&'b [syntax::TypeField]>,
        need_vis: bool,
        is_ref: bool,
    ) -> RcDoc<'b> {
        let old = if self.state.path.last() == Some(&"record".to_string()) {
            // don't push record again when coming from pp_ty
            None
        } else {
            Some(self.state.push_state(&StateElem::TypeStr("record")))
        };
        let res = if is_tuple(fs) {
            self.pp_tuple(fs, need_vis, is_ref)
        } else {
            let fields: Vec<_> = fs
                .iter()
                .map(|f| {
                    let (docs, syntax_field) = find_field(syntax, &f.id);
                    docs.append(self.pp_record_field(f, syntax_field, need_vis, is_ref))
                })
                .collect();
            let fields = concat(fields.into_iter(), ",");
            enclose_space("{", fields, "}")
        };
        if let Some(old) = old {
            self.state.pop_state(old, StateElem::TypeStr("record"));
        }
        res
    }

    fn pp_variant<'b>(
        &mut self,
        fs: &'b [Field],
        syntax: Option<&'b [syntax::TypeField]>,
        is_ref: bool,
    ) -> RcDoc<'b> {
        // only possible for result variant
        if let Some((ok, err, is_motoko)) = as_result(fs) {
            // This is a hacky way to redirect Result type
            let old = self
                .state
                .push_state(&StateElem::TypeStr("std::result::Result"));
            let result = if let Some(t) = &self.state.config.use_type {
                let (res, _) = parse_use_type(t);
                // not generating test for this use_type. rustc should be able to catch type mismatches.
                self.state.update_stats("use_type");
                res
            } else if is_motoko {
                "candid::MotokoResult".to_string()
            } else {
                "std::result::Result".to_string()
            };
            self.state
                .pop_state(old, StateElem::TypeStr("std::result::Result"));
            let old = self.state.push_state(&StateElem::Label("Ok"));
            let ok = self.pp_ty(ok, is_ref);
            self.state.pop_state(old, StateElem::Label("Ok"));
            let old = self.state.push_state(&StateElem::Label("Err"));
            let err = self.pp_ty(err, is_ref);
            self.state.pop_state(old, StateElem::Label("Err"));
            let body = ok.append(", ").append(err);
            RcDoc::text(result).append(enclose("<", body, ">"))
        } else {
            self.pp_variant_fields(fs, syntax)
        }
    }

    fn pp_variant_field<'b>(&mut self, field: &'b Field, syntax: Option<&'b IDLType>) -> RcDoc<'b> {
        let lab = field.id.to_string();
        let old = self.state.push_state(&StateElem::Label(&lab));
        let res = match (field.ty.as_ref(), syntax) {
            (TypeInner::Null, _) => self.pp_label(&field.id, true, false),
            (TypeInner::Record(fs), _) => self
                .pp_label(&field.id, true, false)
                .append(self.pp_record_fields(fs, None, false, false)),
            (_, _) => self.pp_label(&field.id, true, false).append(enclose(
                "(",
                self.pp_ty_rich(&field.ty, syntax, false),
                ")",
            )),
        };
        self.state.pop_state(old, StateElem::Label(&lab));
        res
    }

    fn pp_variant_fields<'b>(
        &mut self,
        fs: &'b [Field],
        syntax: Option<&'b [syntax::TypeField]>,
    ) -> RcDoc<'b> {
        let old = self.state.push_state(&StateElem::TypeStr("variant"));
        let fields: Vec<_> = fs
            .iter()
            .map(|f| {
                let (docs, syntax_field) = find_field(syntax, &f.id);
                docs.append(self.pp_variant_field(f, syntax_field))
            })
            .collect();
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
            let syntax = self.prog.lookup(id);
            let syntax_ty = syntax.map(|b| &b.typ);
            let docs = syntax
                .map(|b| pp_docs(b.docs.as_ref()))
                .unwrap_or(RcDoc::nil());
            self.state.update_stats("name");
            self.state.update_stats("visibility");
            self.state.update_stats("attributes");
            let vis = pp_vis(&self.state.config.visibility);
            let derive = self
                .state
                .config
                .attributes
                .clone()
                .map(RcDoc::text)
                .unwrap_or(RcDoc::text("#[derive(CandidType, Deserialize)]"));
            let derive = docs.append(derive).append(RcDoc::line());
            let line = match ty.as_ref() {
                TypeInner::Record(fs) => {
                    let separator = if is_tuple(fs) {
                        RcDoc::text(";")
                    } else {
                        RcDoc::nil()
                    };
                    let syntax_fields = syntax_ty.and_then(|t| {
                        if let IDLType::RecordT(syntax_fields) = &t {
                            Some(syntax_fields.as_slice())
                        } else {
                            None
                        }
                    });
                    derive
                        .append(vis)
                        .append("struct ")
                        .append(name)
                        .append(" ")
                        .append(self.pp_record_fields(fs, syntax_fields, true, false))
                        .append(separator)
                }
                TypeInner::Variant(fs) => {
                    if as_result(fs).is_some() {
                        vis.append(kwd("type"))
                            .append(name)
                            .append(" = ")
                            .append(self.pp_ty_rich(ty, syntax_ty, false))
                            .append(";")
                    } else {
                        let syntax_fields = syntax_ty.and_then(|t| {
                            if let IDLType::VariantT(syntax_fields) = &t {
                                Some(syntax_fields.as_slice())
                            } else {
                                None
                            }
                        });
                        derive
                            .append(vis)
                            .append("enum ")
                            .append(name)
                            .append(" ")
                            .append(self.pp_variant_fields(fs, syntax_fields))
                    }
                }
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
                            .append(vis.clone())
                            .append("struct ")
                            .append(name)
                            // TODO: Unfortunately, the visibility of the inner newtype is also controlled by var.visibility
                            .append(enclose(
                                "(",
                                vis.append(self.pp_ty_rich(ty, syntax_ty, false)),
                                ")",
                            ))
                            .append(";")
                    } else {
                        vis.append(kwd("type"))
                            .append(name)
                            .append(" = ")
                            .append(self.pp_ty_rich(ty, syntax_ty, false))
                            .append(";")
                    }
                }
            };
            self.state.pop_state(old, StateElem::Label(id));
            res.push(line)
        }
        lines(res.into_iter())
    }
    fn pp_args<'b>(&mut self, args: &'b [ArgType], prefix: &'b str) -> RcDoc<'b> {
        let doc: Vec<_> = args
            .iter()
            .enumerate()
            .map(|(i, t)| {
                let lab = t.name.clone().unwrap_or_else(|| format!("{prefix}{i}"));
                let old = self.state.push_state(&StateElem::Label(&lab));
                let res = self.pp_ty(&t.typ, true);
                self.state.pop_state(old, StateElem::Label(&lab));
                res
            })
            .collect();
        let doc = concat(doc.into_iter(), ",");
        enclose("(", doc, ")")
    }
    fn pp_rets<'b>(&mut self, args: &'b [Type], prefix: &'b str) -> RcDoc<'b> {
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
        let rets = self.pp_rets(&f.rets, "ret");
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

    fn pp_function(
        &mut self,
        id: &str,
        func: &Function,
        syntax: Option<&syntax::Binding>,
    ) -> Method {
        use candid::types::internal::FuncMode;
        let old = self.state.push_state(&StateElem::Label(id));
        let name = self
            .state
            .config
            .name
            .clone()
            .unwrap_or_else(|| ident(id, Some(Case::Snake)).pretty(LINE_WIDTH).to_string());
        self.state.update_stats("name");
        let args: Vec<_> = func
            .args
            .iter()
            .enumerate()
            .map(|(i, arg)| {
                let lab = arg.name.clone().unwrap_or_else(|| format!("arg{i}"));
                let old = self.state.push_state(&StateElem::Label(&lab));
                let name = self
                    .state
                    .config
                    .name
                    .clone()
                    .unwrap_or_else(|| lab.clone());
                self.state.update_stats("name");
                let res = self.pp_ty(&arg.typ, true);
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
            docs: syntax.map(|b| b.docs.clone()).unwrap_or_default(),
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
                .map(|(i, arg)| {
                    let lab = arg.name.clone().unwrap_or_else(|| format!("arg{i}"));
                    let old = self.state.push_state(&StateElem::Label(&lab));
                    let name = self
                        .state
                        .config
                        .name
                        .clone()
                        .unwrap_or_else(|| lab.clone());
                    self.state.update_stats("name");
                    let res = self.pp_ty(&arg.typ, true);
                    self.state.pop_state(old, StateElem::Label(&lab));
                    (name, res.pretty(LINE_WIDTH).to_string())
                })
                .collect();
            self.state.pop_state(old, StateElem::Label("init"));
            Some(args)
        } else {
            None
        };

        let mut res = Vec::new();
        let serv = self.state.env.as_service(&actor).unwrap();
        let syntax_methods = self.prog.resolve_actor_methods().unwrap();
        for (id, func) in serv.iter() {
            let func = self.state.env.as_func(func).unwrap();
            let syntax = syntax_methods.iter().find(|b| b.id == *id);
            res.push(self.pp_function(id, func, syntax));
        }
        (res, init)
    }
}

#[derive(Serialize, Debug)]
pub struct Output {
    pub type_defs: String,
    pub methods: Vec<Method>,
    pub init_args: Option<Vec<(String, String)>>,
    pub tests: String,
    pub actor_docs: Vec<String>,
}

#[derive(Serialize, Debug)]
pub struct Method {
    pub name: String,
    pub original_name: String,
    pub args: Vec<(String, String)>,
    pub rets: Vec<String>,
    pub mode: String,
    pub docs: Vec<String>,
}

pub fn emit_bindgen(
    tree: &Config,
    env: &TypeEnv,
    actor: &Option<Type>,
    prog: &mut IDLMergedProg,
) -> (Output, Vec<String>) {
    let mut state = NominalState {
        state: crate::configs::State::new(&tree.0, env),
        prog,
    };
    let (env, actor) = state.nominalize_all(actor);
    let old_stats = state.state.stats.clone();
    let def_list = if let Some(actor) = &actor {
        chase_actor(&env, actor).unwrap()
    } else {
        env.0.iter().map(|pair| pair.0.as_ref()).collect::<Vec<_>>()
    };
    let recs = infer_rec(&env, &def_list).unwrap();
    let mut state = State {
        state: crate::configs::State::new(&tree.0, &env),
        prog,
        recs,
        tests: BTreeMap::new(),
    };
    state.state.stats = old_stats;
    let defs = state.pp_defs(&def_list);
    let (methods, init_args, actor_docs) = if let Some(actor) = &actor {
        let (meths, args) = state.pp_actor(actor);
        let syntax_actor = prog.resolve_actor().ok().flatten();
        let docs = syntax_actor.map(|a| a.docs.clone()).unwrap_or_default();
        (meths, args, docs)
    } else {
        (Vec::new(), None, Vec::new())
    };
    let tests = state.tests.into_values().collect::<Vec<_>>().join("\n");
    let unused = state.state.report_unused();
    (
        Output {
            type_defs: defs.pretty(LINE_WIDTH).to_string(),
            methods,
            init_args,
            tests,
            actor_docs,
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
        tests: String,
        actor_docs: Vec<String>,
    }
    let data = HBOutput {
        type_defs: output.type_defs,
        methods: output.methods,
        external: config.0,
        init_args: output.init_args,
        tests: output.tests,
        actor_docs: output.actor_docs,
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
                ("doc_comment_prefix", DOC_COMMENT_PREFIX),
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
    prog: &IDLMergedProg,
    mut external: ExternalConfig,
) -> (String, Vec<String>) {
    let mut prog = prog.clone();
    let source = match external.0.get("target").map(|s| s.as_str()) {
        Some("canister_call") | None => Cow::Borrowed(include_str!("rust_call.hbs")),
        Some("agent") => Cow::Borrowed(include_str!("rust_agent.hbs")),
        Some("stub") => {
            let metadata = crate::utils::get_metadata(env, actor);
            if let Some(metadata) = metadata {
                external.0.insert("metadata".to_string(), metadata);
            }
            Cow::Borrowed(include_str!("rust_stub.hbs"))
        }
        Some("custom") => {
            let template = external
                .0
                .get("template")
                .expect("template field expected for custom target");
            Cow::Owned(std::fs::read_to_string(template).unwrap())
        }
        _ => unimplemented!(),
    };
    let (output, unused) = emit_bindgen(tree, env, actor, &mut prog);
    (output_handlebar(output, external, &source), unused)
}

pub enum TypePath {
    Id(String),
    Opt,
    Vec,
    RecordField(String),
    VariantField(String),
    ResultField(String),
    Func(String),
    Init,
}
fn path_to_var(path: &[TypePath]) -> String {
    let name: Vec<&str> = path
        .iter()
        .map(|node| match node {
            TypePath::Id(id) => id.as_str(),
            TypePath::RecordField(f) | TypePath::VariantField(f) | TypePath::ResultField(f) => {
                f.as_str()
            }
            TypePath::Opt => "inner",
            TypePath::Vec => "item",
            TypePath::Func(id) => id.as_str(),
            TypePath::Init => "init",
        })
        .collect();
    name.join("_").to_case(Case::Pascal)
}
struct NominalState<'a> {
    state: crate::configs::State<'a, BindingConfig>,
    prog: &'a mut IDLMergedProg,
}
impl NominalState<'_> {
    // Convert structural typing to nominal typing to fit Rust's type system
    fn nominalize(
        &mut self,
        env: &mut TypeEnv,
        path: &mut Vec<TypePath>,
        t: &Type,
        syntax: Option<&IDLType>,
    ) -> Type {
        let elem = StateElem::Type(t);
        let old = if matches!(t.as_ref(), TypeInner::Func(_)) {
            // strictly speaking, we want to avoid func label from the main service. But this is probably good enough.
            None
        } else {
            Some(self.state.push_state(&elem))
        };
        let res = match t.as_ref() {
            TypeInner::Opt(ty) => {
                path.push(TypePath::Opt);
                let syntax_ty = syntax.and_then(|s| {
                    if let IDLType::OptT(inner) = s {
                        Some(inner.as_ref())
                    } else {
                        None
                    }
                });
                let ty = self.nominalize(env, path, ty, syntax_ty);
                path.pop();
                TypeInner::Opt(ty)
            }
            TypeInner::Vec(ty) => {
                path.push(TypePath::Vec);
                let syntax_ty = syntax.and_then(|s| {
                    if let IDLType::VecT(inner) = s {
                        Some(inner.as_ref())
                    } else {
                        None
                    }
                });
                let ty = self.nominalize(env, path, ty, syntax_ty);
                path.pop();
                TypeInner::Vec(ty)
            }
            TypeInner::Record(fs) => {
                let syntax_fields = syntax.and_then(|s| {
                    if let IDLType::RecordT(syntax_fields) = s {
                        Some(syntax_fields)
                    } else {
                        None
                    }
                });
                if matches!(
                    path.last(),
                    None | Some(TypePath::VariantField(_)) | Some(TypePath::Id(_))
                ) || is_tuple(fs)
                {
                    let fs: Vec<_> = fs
                        .iter()
                        .map(|Field { id, ty }| {
                            let lab = id.to_string();
                            let elem = StateElem::Label(&lab);
                            let old = self.state.push_state(&elem);
                            path.push(TypePath::RecordField(id.to_string()));
                            let syntax_field = syntax_fields.and_then(|s| {
                                s.iter().find(|f| f.label == **id).map(|f| f.typ.clone())
                            });
                            let ty = self.nominalize(env, path, ty, syntax_field.as_ref());
                            path.pop();
                            self.state.pop_state(old, elem);
                            Field { id: id.clone(), ty }
                        })
                        .collect();
                    TypeInner::Record(fs)
                } else {
                    let new_var = if let Some(name) = &self.state.config.name {
                        let res = name.to_string();
                        self.state.update_stats("name");
                        res
                    } else {
                        path_to_var(path)
                    };
                    let new_syntax = IDLType::RecordT(syntax_fields.cloned().unwrap_or_default());
                    let ty = self.nominalize(
                        env,
                        &mut vec![TypePath::Id(new_var.clone())],
                        &TypeInner::Record(fs.to_vec()).into(),
                        Some(&new_syntax),
                    );
                    env.0.insert(new_var.clone(), ty);
                    self.prog
                        .insert_binding(new_var.clone(), new_syntax, vec![]);
                    TypeInner::Var(new_var)
                }
            }
            TypeInner::Variant(fs) => {
                let syntax_fields = syntax.and_then(|s| {
                    if let IDLType::VariantT(syntax_fields) = s {
                        Some(syntax_fields)
                    } else {
                        None
                    }
                });
                let is_result = as_result(fs).is_some();
                if matches!(path.last(), None | Some(TypePath::Id(_))) || is_result {
                    let fs: Vec<_> = fs
                        .iter()
                        .map(|Field { id, ty }| {
                            let lab = id.to_string();
                            let old = self.state.push_state(&StateElem::Label(&lab));
                            if is_result {
                                // so that inner record gets a new name
                                path.push(TypePath::ResultField(id.to_string()));
                            } else {
                                path.push(TypePath::VariantField(id.to_string()));
                            }
                            let syntax_field = syntax_fields.and_then(|s| {
                                s.iter().find(|f| f.label == **id).map(|f| f.typ.clone())
                            });
                            let ty = self.nominalize(env, path, ty, syntax_field.as_ref());
                            path.pop();
                            self.state.pop_state(old, StateElem::Label(&lab));
                            Field { id: id.clone(), ty }
                        })
                        .collect();
                    TypeInner::Variant(fs)
                } else {
                    let new_var = if let Some(name) = &self.state.config.name {
                        let res = name.to_string();
                        self.state.update_stats("name");
                        res
                    } else {
                        path_to_var(path)
                    };
                    let new_syntax = IDLType::VariantT(syntax_fields.cloned().unwrap_or_default());
                    let ty = self.nominalize(
                        env,
                        &mut vec![TypePath::Id(new_var.clone())],
                        &TypeInner::Variant(fs.to_vec()).into(),
                        Some(&new_syntax),
                    );
                    env.0.insert(new_var.clone(), ty);
                    self.prog
                        .insert_binding(new_var.clone(), new_syntax, vec![]);
                    TypeInner::Var(new_var)
                }
            }
            TypeInner::Func(func) => match path.last() {
                None | Some(TypePath::Id(_)) => {
                    let func = func.clone();
                    TypeInner::Func(Function {
                        modes: func.modes,
                        args: func
                            .args
                            .into_iter()
                            .enumerate()
                            .map(|(i, arg)| {
                                let lab = arg.name.clone().unwrap_or_else(|| format!("arg{i}"));
                                let old = self.state.push_state(&StateElem::Label(&lab));
                                let idx = if i == 0 {
                                    "".to_string()
                                } else {
                                    i.to_string()
                                };
                                path.push(TypePath::Func(format!("arg{idx}")));
                                let ty = self.nominalize(env, path, &arg.typ, None);
                                path.pop();
                                self.state.pop_state(old, StateElem::Label(&lab));
                                ArgType {
                                    name: arg.name.clone(),
                                    typ: ty,
                                }
                            })
                            .collect(),
                        rets: func
                            .rets
                            .into_iter()
                            .enumerate()
                            .map(|(i, ty)| {
                                let lab = format!("ret{i}");
                                let old = self.state.push_state(&StateElem::Label(&lab));
                                let idx = if i == 0 {
                                    "".to_string()
                                } else {
                                    i.to_string()
                                };
                                path.push(TypePath::Func(format!("ret{idx}")));
                                let ty = self.nominalize(env, path, &ty, None);
                                path.pop();
                                self.state.pop_state(old, StateElem::Label(&lab));
                                ty
                            })
                            .collect(),
                    })
                }
                Some(_) => {
                    let new_var = if let Some(name) = &self.state.config.name {
                        let res = name.to_string();
                        self.state.update_stats("name");
                        res
                    } else {
                        path_to_var(path)
                    };
                    let ty = self.nominalize(
                        env,
                        &mut vec![TypePath::Id(new_var.clone())],
                        &TypeInner::Func(func.clone()).into(),
                        None,
                    );
                    env.0.insert(new_var.clone(), ty);
                    TypeInner::Var(new_var)
                }
            },
            TypeInner::Service(serv) => match path.last() {
                None | Some(TypePath::Id(_)) => TypeInner::Service(
                    serv.iter()
                        .map(|(meth, ty)| {
                            let lab = meth.to_string();
                            let old = self.state.push_state(&StateElem::Label(&lab));
                            path.push(TypePath::Id(meth.to_string()));
                            let ty = self.nominalize(env, path, ty, None);
                            path.pop();
                            self.state.pop_state(old, StateElem::Label(&lab));
                            (meth.clone(), ty)
                        })
                        .collect(),
                ),
                Some(_) => {
                    let new_var = if let Some(name) = &self.state.config.name {
                        let res = name.to_string();
                        self.state.update_stats("name");
                        res
                    } else {
                        path_to_var(path)
                    };
                    let ty = self.nominalize(
                        env,
                        &mut vec![TypePath::Id(new_var.clone())],
                        &TypeInner::Service(serv.clone()).into(),
                        None,
                    );
                    env.0.insert(new_var.clone(), ty);
                    TypeInner::Var(new_var)
                }
            },
            TypeInner::Class(args, ty) => {
                let syntax_ty = syntax.and_then(|s| {
                    if let IDLType::ClassT(_, syntax_ty) = s {
                        Some(syntax_ty.as_ref())
                    } else {
                        None
                    }
                });
                TypeInner::Class(
                    args.iter()
                        .map(|arg| {
                            let elem = StateElem::Label("init");
                            let old = self.state.push_state(&elem);
                            path.push(TypePath::Init);
                            let ty = self.nominalize(env, path, &arg.typ, None);
                            path.pop();
                            self.state.pop_state(old, elem);
                            ArgType {
                                name: arg.name.clone(),
                                typ: ty,
                            }
                        })
                        .collect(),
                    self.nominalize(env, path, ty, syntax_ty),
                )
            }
            t => t.clone(),
        }
        .into();
        if let Some(old) = old {
            self.state.pop_state(old, elem);
        }
        res
    }

    fn nominalize_all(&mut self, actor: &Option<Type>) -> (TypeEnv, Option<Type>) {
        let mut res = TypeEnv(Default::default());
        for (id, ty) in self.state.env.0.iter() {
            let elem = StateElem::Label(id);
            let old = self.state.push_state(&elem);
            let syntax = self.prog.lookup(id).map(|t| t.typ.clone());
            let ty = self.nominalize(
                &mut res,
                &mut vec![TypePath::Id(id.clone())],
                ty,
                syntax.as_ref(),
            );
            res.0.insert(id.to_string(), ty);
            self.state.pop_state(old, elem);
        }
        let actor = actor
            .as_ref()
            .map(|ty| self.nominalize(&mut res, &mut vec![], ty, None));
        (res, actor)
    }
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
