use super::analysis::{chase_actor, infer_rec};
use crate::parser::typing::TypeEnv;
use crate::pretty::*;
use crate::types::{Field, Function, Label, Type};
use pretty::RcDoc;
use std::collections::BTreeSet;

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
fn ident_(id: &str) -> (RcDoc, bool) {
    if id.is_empty()
        || id.starts_with(|c: char| !c.is_ascii_alphabetic() && c != '_')
        || id.chars().any(|c| !c.is_ascii_alphanumeric() && c != '_')
    {
        (RcDoc::as_string(format!("_{}_", crate::idl_hash(id))), true)
    } else if ["crate", "self", "super", "Self"].contains(&id) {
        (str(id).append("_"), true)
    } else if KEYWORDS.contains(&id) {
        (str("r#").append(id), false)
    } else {
        (str(id), false)
    }
}
fn ident(id: &str) -> RcDoc {
    ident_(id).0
}
fn field_name(id: &str) -> RcDoc {
    let (doc, is_rename) = ident_(id);
    if is_rename {
        str("#[serde(rename=\"")
            .append(id.escape_debug().to_string())
            .append("\")]")
            .append(RcDoc::line())
            .append(doc)
    } else {
        doc
    }
}

fn pp_ty<'a, 'b>(ty: &'a Type, recs: &'b RecPoints) -> RcDoc<'a> {
    use Type::*;
    match *ty {
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
            let name = ident(id);
            if recs.contains(id.as_str()) {
                str("Box<").append(name).append(">")
            } else {
                name
            }
        }
        Principal => str("candid::Principal"),
        Opt(ref t) => str("Option").append(enclose("<", pp_ty(t, recs), ">")),
        Vec(ref t) => str("Vec").append(enclose("<", pp_ty(t, recs), ">")),
        Record(ref fs) => pp_record_fields(fs, recs),
        Variant(_) => unreachable!(), // not possible after rewriting
        Func(_) => str("candid::Func"),
        Service(_) => str("candid::Service"),
        Class(_, _) => unreachable!(),
        Knot(_) | Unknown => unreachable!(),
    }
}

fn pp_label(id: &Label) -> RcDoc {
    match id {
        Label::Named(str) => field_name(str),
        Label::Id(n) | Label::Unnamed(n) => str("_").append(RcDoc::as_string(n)).append("_"),
    }
}

fn pp_record_field<'a, 'b>(field: &'a Field, recs: &'b RecPoints) -> RcDoc<'a> {
    pp_label(&field.id)
        .append(kwd(":"))
        .append(pp_ty(&field.ty, recs))
}

fn pp_record_fields<'a, 'b>(fs: &'a [Field], recs: &'b RecPoints) -> RcDoc<'a> {
    if is_tuple(fs) {
        let tuple = RcDoc::concat(fs.iter().map(|f| pp_ty(&f.ty, recs).append(",")));
        enclose("(", tuple, ")")
    } else {
        let fields = concat(fs.iter().map(|f| pp_record_field(f, recs)), ",");
        enclose_space("{", fields, "}")
    }
}

fn pp_variant_field<'a, 'b>(field: &'a Field, recs: &'b RecPoints) -> RcDoc<'a> {
    match &field.ty {
        Type::Null => pp_label(&field.id),
        Type::Record(fs) => pp_label(&field.id).append(pp_record_fields(fs, recs)),
        _ => pp_label(&field.id).append(enclose("(", pp_ty(&field.ty, recs), ")")),
    }
}

fn pp_variant_fields<'a, 'b>(fs: &'a [Field], recs: &'b RecPoints) -> RcDoc<'a> {
    let fields = concat(fs.iter().map(|f| pp_variant_field(f, recs)), ",");
    enclose_space("{", fields, "}")
}

fn pp_defs<'a>(env: &'a TypeEnv, def_list: &'a [&'a str], recs: &'a RecPoints) -> RcDoc<'a> {
    let derive = "#[derive(CandidType, Deserialize)]";
    lines(def_list.iter().map(|id| {
        let ty = env.find_type(id).unwrap();
        let name = ident(id).append(" ");
        match ty {
            Type::Record(fs) => str(derive)
                .append(RcDoc::line())
                .append("struct ")
                .append(name)
                .append(pp_record_fields(fs, recs))
                .append(RcDoc::hardline()),
            Type::Variant(fs) => str(derive)
                .append(RcDoc::line())
                .append("enum ")
                .append(name)
                .append(pp_variant_fields(fs, recs))
                .append(RcDoc::hardline()),
            _ => {
                if recs.contains(id) {
                    str(derive)
                        .append(RcDoc::line())
                        .append("struct ")
                        .append(ident(id))
                        .append(enclose("(", pp_ty(ty, recs), ")"))
                        .append(";")
                        .append(RcDoc::hardline())
                } else {
                    kwd("type")
                        .append(name)
                        .append("= ")
                        .append(pp_ty(ty, recs))
                        .append(";")
                }
            }
        }
    }))
}

fn pp_function<'a>(id: &'a str, func: &'a Function) -> RcDoc<'a> {
    let name = ident(id);
    let empty = BTreeSet::new();
    let args = concat(
        std::iter::once(str("&self")).chain(
            func.args
                .iter()
                .enumerate()
                .map(|(i, ty)| RcDoc::as_string(format!("arg{}: ", i)).append(pp_ty(ty, &empty))),
        ),
        ",",
    );
    let rets = enclose(
        "(",
        RcDoc::concat(func.rets.iter().map(|ty| pp_ty(ty, &empty).append(","))),
        ")",
    );
    let sig = kwd("pub async fn")
        .append(name)
        .append(enclose("(", args, ")"))
        .append(kwd(" ->"))
        .append(enclose("CallResult<", rets, "> "));
    let args = RcDoc::concat((0..func.args.len()).map(|i| RcDoc::text(format!("arg{},", i))));
    let method = id.escape_debug().to_string();
    let body = str("ic_cdk::call(self.0, \"")
        .append(method)
        .append("\", ")
        .append(enclose("(", args, ")"))
        .append(").await");
    sig.append(enclose_space("{", body, "}"))
}

fn pp_actor<'a>(env: &'a TypeEnv, actor: &'a Type) -> RcDoc<'a> {
    // TODO trace to service before we figure out what canister means in Rust
    let serv = env.as_service(actor).unwrap();
    let body = RcDoc::intersperse(
        serv.iter().map(|(id, func)| {
            let func = env.as_func(func).unwrap();
            pp_function(id, func)
        }),
        RcDoc::hardline(),
    );
    RcDoc::text("struct SERVICE(candid::Principal);")
        .append(RcDoc::hardline())
        .append("impl SERVICE")
        .append(enclose_space("{", body, "}"))
}

pub fn compile(env: &TypeEnv, actor: &Option<Type>) -> String {
    let header = r#"// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
use ic_cdk::export::candid::{self, CandidType, Deserialize};
use ic_cdk::api::call::CallResult;
"#;
    let (env, actor) = nominalize_all(env, actor);
    let def_list: Vec<_> = if let Some(actor) = &actor {
        chase_actor(&env, actor).unwrap()
    } else {
        env.0.iter().map(|pair| pair.0.as_ref()).collect()
    };
    let recs = infer_rec(&env, &def_list).unwrap();
    let defs = pp_defs(&env, &def_list, &recs);
    let doc = match &actor {
        None => defs,
        Some(actor) => {
            let actor = pp_actor(&env, actor);
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
    name.join("_")
}
// Convert structural typing to nominal typing to fit Rust's type system
fn nominalize(env: &mut TypeEnv, path: &mut Vec<TypePath>, t: Type) -> Type {
    match t {
        Type::Opt(ty) => {
            path.push(TypePath::Opt);
            let ty = nominalize(env, path, *ty);
            path.pop();
            Type::Opt(Box::new(ty))
        }
        Type::Vec(ty) => {
            path.push(TypePath::Opt);
            let ty = nominalize(env, path, *ty);
            path.pop();
            Type::Vec(Box::new(ty))
        }
        Type::Record(fs) => {
            if matches!(
                path.last(),
                None | Some(TypePath::VariantField(_)) | Some(TypePath::Id(_))
            ) || is_tuple(&fs)
            {
                let fs: Vec<_> = fs
                    .into_iter()
                    .map(|Field { id, ty }| {
                        path.push(TypePath::RecordField(id.to_string()));
                        let ty = nominalize(env, path, ty);
                        path.pop();
                        Field { id, ty }
                    })
                    .collect();
                Type::Record(fs)
            } else {
                let new_var = path_to_var(path);
                let ty = nominalize(
                    env,
                    &mut vec![TypePath::Id(new_var.clone())],
                    Type::Record(fs),
                );
                env.0.insert(new_var.clone(), ty);
                Type::Var(new_var)
            }
        }
        Type::Variant(fs) => match path.last() {
            None | Some(TypePath::Id(_)) => {
                let fs: Vec<_> = fs
                    .into_iter()
                    .map(|Field { id, ty }| {
                        path.push(TypePath::VariantField(id.to_string()));
                        let ty = nominalize(env, path, ty);
                        path.pop();
                        Field { id, ty }
                    })
                    .collect();
                Type::Variant(fs)
            }
            Some(_) => {
                let new_var = path_to_var(path);
                let ty = nominalize(
                    env,
                    &mut vec![TypePath::Id(new_var.clone())],
                    Type::Variant(fs),
                );
                env.0.insert(new_var.clone(), ty);
                Type::Var(new_var)
            }
        },
        Type::Func(func) => Type::Func(Function {
            modes: func.modes,
            args: func
                .args
                .into_iter()
                .enumerate()
                .map(|(i, ty)| {
                    path.push(TypePath::Func(format!("arg{}", i)));
                    let ty = nominalize(env, path, ty);
                    path.pop();
                    ty
                })
                .collect(),
            rets: func
                .rets
                .into_iter()
                .enumerate()
                .map(|(i, ty)| {
                    path.push(TypePath::Func(format!("ret{}", i)));
                    let ty = nominalize(env, path, ty);
                    path.pop();
                    ty
                })
                .collect(),
        }),
        Type::Service(serv) => Type::Service(
            serv.into_iter()
                .map(|(meth, ty)| {
                    path.push(TypePath::Id(meth.to_string()));
                    let ty = nominalize(env, path, ty);
                    path.pop();
                    (meth, ty)
                })
                .collect(),
        ),
        Type::Class(args, ty) => Type::Class(
            args.into_iter()
                .map(|ty| {
                    path.push(TypePath::Init);
                    let ty = nominalize(env, path, ty);
                    path.pop();
                    ty
                })
                .collect(),
            Box::new(nominalize(env, path, *ty)),
        ),
        _ => t,
    }
}

fn nominalize_all(env: &TypeEnv, actor: &Option<Type>) -> (TypeEnv, Option<Type>) {
    let mut res = TypeEnv(Default::default());
    for (id, ty) in env.0.iter() {
        let ty = nominalize(&mut res, &mut vec![TypePath::Id(id.clone())], ty.clone());
        res.0.insert(id.to_string(), ty);
    }
    let actor = actor
        .as_ref()
        .map(|ty| nominalize(&mut res, &mut vec![], ty.clone()));
    (res, actor)
}
