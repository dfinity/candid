use super::javascript::{ident, is_tuple};
use crate::parser::typing::TypeEnv;
use crate::pretty::*;
use crate::types::{Field, Function, Label, Type};
use pretty::RcDoc;

fn pp_ty(ty: &Type) -> RcDoc {
    use Type::*;
    match *ty {
        Null => str("null"),
        Bool => str("boolean"),
        Nat => str("bigint"),
        Int => str("bigint"),
        Nat8 => str("number"),
        Nat16 => str("number"),
        Nat32 => str("number"),
        Nat64 => str("bigint"),
        Int8 => str("number"),
        Int16 => str("number"),
        Int32 => str("number"),
        Int64 => str("bigint"),
        Float32 => str("number"),
        Float64 => str("number"),
        Text => str("string"),
        Reserved => str("any"),
        Empty => str("never"),
        Var(ref s) => ident(s),
        Principal => str("Principal"),
        Opt(ref t) => str("[] | ").append(enclose("[", pp_ty(t), "]")),
        Vec(ref t) => str("Array").append(enclose("<", pp_ty(t), ">")),
        Record(ref fs) => {
            if is_tuple(ty) {
                let tuple = concat(fs.iter().map(|f| pp_ty(&f.ty)), ",");
                enclose("[", tuple, "]")
            } else {
                let fields = concat(fs.iter().map(pp_field), ",");
                enclose_space("{", fields, "}")
            }
        }
        Variant(ref fs) => strict_concat(
            fs.iter().map(|f| enclose_space("{", pp_field(f), "}")),
            " |",
        )
        .nest(INDENT_SPACE),
        Func(_) => str("[Principal, string]"),
        Service(_) => str("Principal"),
        Class(_, _) => unreachable!(),
        Knot(_) | Unknown => unreachable!(),
    }
}

fn pp_label(id: &Label) -> RcDoc {
    match id {
        Label::Named(str) => quote_ident(str),
        Label::Id(n) | Label::Unnamed(n) => str("_")
            .append(RcDoc::as_string(n))
            .append("_")
            .append(RcDoc::space()),
    }
}

fn pp_field(field: &Field) -> RcDoc {
    pp_label(&field.id)
        .append(kwd(":"))
        .append(pp_ty(&field.ty))
}

fn as_ref_ty<'a>(env: &'a TypeEnv, t: &'a Type) -> RcDoc<'a> {
    if let Type::Var(id) = t {
        let ty = env.rec_find_type(id).unwrap();
        match ty {
            Type::Service(_) | Type::Func(_) => pp_ty(ty),
            _ => pp_ty(t),
        }
    } else {
        pp_ty(t)
    }
}

fn pp_function<'a>(env: &'a TypeEnv, func: &'a Function) -> RcDoc<'a> {
    let args = func
        .args
        .iter()
        .enumerate()
        .map(|(i, ty)| RcDoc::text(format!("arg_{}: ", i)).append(as_ref_ty(env, ty)));
    let args = enclose("(", concat(args, ","), ")");
    let rets = str("Promise").append(enclose(
        "<",
        match func.rets.len() {
            0 => str("undefined"),
            1 => as_ref_ty(env, &func.rets[0]),
            _ => enclose(
                "[",
                concat(func.rets.iter().map(|ty| as_ref_ty(env, ty)), ","),
                "]",
            ),
        },
        ">",
    ));
    args.append(" => ").append(rets).nest(INDENT_SPACE)
}

fn pp_service<'a>(env: &'a TypeEnv, serv: &'a [(String, Type)]) -> RcDoc<'a> {
    let doc = concat(
        serv.iter().map(|(id, func)| {
            let func = match func {
                Type::Func(ref func) => pp_function(env, func),
                _ => pp_ty(func),
            };
            quote_ident(id).append(kwd(":")).append(func)
        }),
        ",",
    );
    enclose_space("{", doc, "}")
}

fn pp_defs<'a>(env: &'a TypeEnv, def_list: &'a [&'a str]) -> RcDoc<'a> {
    lines(def_list.iter().map(|id| {
        let ty = env.find_type(id).unwrap();
        let export = match ty {
            Type::Record(_) if !ty.is_tuple() => kwd("export interface")
                .append(ident(id))
                .append(" ")
                .append(pp_ty(ty)),
            Type::Service(ref serv) => kwd("export interface")
                .append(ident(id))
                .append(" ")
                .append(pp_service(env, serv)),
            Type::Func(ref func) => kwd("export type")
                .append(ident(id))
                .append(" = ")
                .append(pp_function(env, func))
                .append(";"),
            _ => kwd("export type")
                .append(ident(id))
                .append(" = ")
                .append(pp_ty(ty))
                .append(";"),
        };
        export.append("")
    }))
}

fn pp_actor<'a>(env: &'a TypeEnv, ty: &'a Type) -> RcDoc<'a> {
    match ty {
        Type::Service(ref serv) => {
            kwd("export interface _SERVICE").append(pp_service(env, serv))
        }
        Type::Var(id) => kwd("export interface _SERVICE extends").append(str(id)).append(str(" {}")),
        Type::Class(_, t) => pp_actor(env, t),
        _ => unreachable!(),
    }
}

pub fn compile(env: &TypeEnv, actor: &Option<Type>) -> String {
    let header = r#"import type { Principal } from '@dfinity/principal';"#;
    let def_list: Vec<_> = env.0.iter().map(|pair| pair.0.as_ref()).collect();
    let defs = pp_defs(env, &def_list);
    let actor = match actor {
        None => RcDoc::nil(),
        Some(actor) => pp_actor(env, actor),
    };
    let doc = RcDoc::text(header)
        .append(RcDoc::line())
        .append(defs)
        .append(actor);
    doc.pretty(LINE_WIDTH).to_string()
}
