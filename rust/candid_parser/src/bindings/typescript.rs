use super::javascript::{ident, is_tuple};
use candid::pretty::utils::*;
use candid::types::{Field, Function, Label, SharedLabel, Type, TypeEnv, TypeInner};
use pretty::RcDoc;

fn pp_ty<'a>(env: &'a TypeEnv, ty: &'a Type, is_ref: bool) -> RcDoc<'a> {
    use TypeInner::*;
    match ty.as_ref() {
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
        Var(ref id) => {
            let ty = env.rec_find_type(id).unwrap();
            if matches!(ty.as_ref(), Func(_)) {
                return pp_inline_func();
            }
            if is_ref && matches!(ty.as_ref(), Service(_)) {
                return pp_inline_service();
            }
            ident(id)
        }
        Principal => str("Principal"),
        Opt(ref t) => str("[] | ").append(enclose("[", pp_ty(env, t, is_ref), "]")),
        Vec(ref t) => {
            let ty = match t.as_ref() {
                Var(ref id) => {
                    let ty = env.rec_find_type(id).unwrap();
                    if matches!(
                        ty.as_ref(),
                        Nat8 | Nat16 | Nat32 | Nat64 | Int8 | Int16 | Int32 | Int64
                    ) {
                        ty
                    } else {
                        t
                    }
                }
                _ => t,
            };
            match ty.as_ref() {
                Nat8 => str("Uint8Array | number[]"),
                Nat16 => str("Uint16Array | number[]"),
                Nat32 => str("Uint32Array | number[]"),
                Nat64 => str("BigUint64Array | bigint[]"),
                Int8 => str("Int8Array | number[]"),
                Int16 => str("Int16Array | number[]"),
                Int32 => str("Int32Array | number[]"),
                Int64 => str("BigInt64Array | bigint[]"),
                _ => str("Array").append(enclose("<", pp_ty(env, t, is_ref), ">")),
            }
        }
        Record(ref fs) => {
            if is_tuple(ty) {
                let tuple = concat(fs.iter().map(|f| pp_ty(env, &f.ty, is_ref)), ",");
                enclose("[", tuple, "]")
            } else {
                let fields = concat(fs.iter().map(|f| pp_field(env, f, is_ref)), ",");
                enclose_space("{", fields, "}")
            }
        }
        Variant(ref fs) => {
            if fs.is_empty() {
                str("never")
            } else {
                strict_concat(
                    fs.iter()
                        .map(|f| enclose_space("{", pp_field(env, f, is_ref), "}")),
                    " |",
                )
                .nest(INDENT_SPACE)
            }
        }
        Func(_) => pp_inline_func(),
        Service(_) => pp_inline_service(),
        Class(_, _) => unreachable!(),
        Knot(_) | Unknown | Future => unreachable!(),
    }
}

fn pp_inline_func<'a>() -> RcDoc<'a> {
    str("[Principal, string]")
}

fn pp_inline_service<'a>() -> RcDoc<'a> {
    str("Principal")
}

fn pp_label(id: &SharedLabel) -> RcDoc {
    match &**id {
        Label::Named(str) => quote_ident(str),
        Label::Id(n) | Label::Unnamed(n) => str("_")
            .append(RcDoc::as_string(n))
            .append("_")
            .append(RcDoc::space()),
    }
}

fn pp_field<'a>(env: &'a TypeEnv, field: &'a Field, is_ref: bool) -> RcDoc<'a> {
    pp_label(&field.id)
        .append(kwd(":"))
        .append(pp_ty(env, &field.ty, is_ref))
}

fn pp_function<'a>(env: &'a TypeEnv, func: &'a Function) -> RcDoc<'a> {
    let args = func.args.iter().map(|arg| pp_ty(env, &arg.typ, true));
    let args = enclose("[", concat(args, ","), "]");
    let rets = match func.rets.len() {
        0 => str("undefined"),
        1 => pp_ty(env, &func.rets[0], true),
        _ => enclose(
            "[",
            concat(func.rets.iter().map(|ty| pp_ty(env, ty, true)), ","),
            "]",
        ),
    };
    enclose(
        "ActorMethod<",
        strict_concat([args, rets].iter().cloned(), ","),
        ">",
    )
}

fn pp_service<'a>(env: &'a TypeEnv, serv: &'a [(String, Type)]) -> RcDoc<'a> {
    let doc = concat(
        serv.iter().map(|(id, func)| {
            let func = match func.as_ref() {
                TypeInner::Func(ref func) => pp_function(env, func),
                TypeInner::Var(ref id) => ident(id),
                _ => unreachable!(),
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
        let export = match ty.as_ref() {
            TypeInner::Record(_) if !ty.is_tuple() => kwd("export interface")
                .append(ident(id))
                .append(" ")
                .append(pp_ty(env, ty, false)),
            TypeInner::Service(ref serv) => kwd("export interface")
                .append(ident(id))
                .append(" ")
                .append(pp_service(env, serv)),
            TypeInner::Func(ref func) => kwd("export type")
                .append(ident(id))
                .append(" = ")
                .append(pp_function(env, func))
                .append(";"),
            TypeInner::Var(ref inner_id) => kwd("export type")
                .append(ident(id))
                .append(" = ")
                .append(ident(inner_id))
                .append(";"),
            _ => kwd("export type")
                .append(ident(id))
                .append(" = ")
                .append(pp_ty(env, ty, false))
                .append(";"),
        };
        export
    }))
}

fn pp_actor<'a>(env: &'a TypeEnv, ty: &'a Type) -> RcDoc<'a> {
    match ty.as_ref() {
        TypeInner::Service(ref serv) => {
            kwd("export interface _SERVICE").append(pp_service(env, serv))
        }
        TypeInner::Var(id) => kwd("export interface _SERVICE extends")
            .append(str(id))
            .append(str(" {}")),
        TypeInner::Class(_, t) => pp_actor(env, t),
        _ => unreachable!(),
    }
}

pub fn compile(env: &TypeEnv, actor: &Option<Type>) -> String {
    let header = r#"import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';
import type { IDL } from '@dfinity/candid';
"#;
    let def_list: Vec<_> = env.0.iter().map(|pair| pair.0.as_ref()).collect();
    let defs = pp_defs(env, &def_list);
    let actor = match actor {
        None => RcDoc::nil(),
        Some(actor) => pp_actor(env, actor)
            .append(RcDoc::line())
            .append("export declare const idlFactory: IDL.InterfaceFactory;")
            .append(RcDoc::line())
            .append("export declare const init: (args: { IDL: typeof IDL }) => IDL.Type[];"),
    };
    let doc = RcDoc::text(header)
        .append(RcDoc::line())
        .append(defs)
        .append(actor);
    doc.pretty(LINE_WIDTH).to_string()
}
