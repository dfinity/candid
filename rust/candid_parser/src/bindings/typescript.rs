use super::javascript::{ident, is_tuple_fields};
use crate::syntax::{self, IDLMergedProg, IDLType};
use candid::pretty::utils::*;
use candid::types::{Field, Function, Label, SharedLabel, Type, TypeEnv, TypeInner};
use pretty::RcDoc;

const DOC_COMMENT_PREFIX: &str = "/**";
const DOC_COMMENT_LINE_PREFIX: &str = " * ";
const DOC_COMMENT_SUFFIX: &str = " */";

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

fn pp_ty_rich<'a>(
    env: &'a TypeEnv,
    ty: &'a Type,
    syntax: Option<&'a IDLType>,
    is_ref: bool,
) -> RcDoc<'a> {
    match (ty.as_ref(), syntax) {
        (TypeInner::Record(ref fields), Some(IDLType::RecordT(syntax_fields))) => {
            pp_record(env, fields, Some(syntax_fields), is_ref)
        }
        (TypeInner::Variant(ref fields), Some(IDLType::VariantT(syntax_fields))) => {
            pp_variant(env, fields, Some(syntax_fields), is_ref)
        }
        (TypeInner::Service(ref serv), Some(IDLType::ServT(syntax_serv))) => {
            pp_service(env, serv, Some(syntax_serv))
        }
        (TypeInner::Opt(ref t), Some(IDLType::OptT(syntax_inner))) => {
            pp_opt(env, t, Some(syntax_inner), is_ref)
        }
        (TypeInner::Vec(ref t), Some(IDLType::VecT(syntax_inner))) => {
            pp_vec(env, t, Some(syntax_inner), is_ref)
        }
        (_, _) => pp_ty(env, ty, is_ref),
    }
}

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
        Opt(ref t) => pp_opt(env, t, None, is_ref),
        Vec(ref t) => pp_vec(env, t, None, is_ref),
        Record(ref fs) => pp_record(env, fs, None, is_ref),
        Variant(ref fs) => pp_variant(env, fs, None, is_ref),
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

fn pp_vec<'a>(
    env: &'a TypeEnv,
    inner: &'a Type,
    syntax: Option<&'a IDLType>,
    is_ref: bool,
) -> RcDoc<'a> {
    use TypeInner::*;
    let ty = match inner.as_ref() {
        Var(ref id) => {
            let ty = env.rec_find_type(id).unwrap();
            if matches!(
                ty.as_ref(),
                Nat8 | Nat16 | Nat32 | Nat64 | Int8 | Int16 | Int32 | Int64
            ) {
                ty
            } else {
                inner
            }
        }
        _ => inner,
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
        _ => str("Array").append(enclose("<", pp_ty_rich(env, inner, syntax, is_ref), ">")),
    }
}

fn pp_field<'a>(
    env: &'a TypeEnv,
    field: &'a Field,
    syntax: Option<&'a IDLType>,
    is_ref: bool,
) -> RcDoc<'a> {
    pp_label(&field.id)
        .append(kwd(":"))
        .append(pp_ty_rich(env, &field.ty, syntax, is_ref))
}

fn pp_record<'a>(
    env: &'a TypeEnv,
    fields: &'a [Field],
    syntax: Option<&'a [syntax::TypeField]>,
    is_ref: bool,
) -> RcDoc<'a> {
    if is_tuple_fields(fields) {
        let tuple = concat(fields.iter().map(|f| pp_ty(env, &f.ty, is_ref)), ",");
        enclose("[", tuple, "]")
    } else {
        let fields = concat(
            fields.iter().map(|f| {
                let (docs, syntax_field) = find_field(syntax, &f.id);
                docs.append(pp_field(env, f, syntax_field, is_ref))
            }),
            ",",
        );
        enclose_space("{", fields, "}")
    }
}

fn pp_variant<'a>(
    env: &'a TypeEnv,
    fields: &'a [Field],
    syntax: Option<&'a [syntax::TypeField]>,
    is_ref: bool,
) -> RcDoc<'a> {
    if fields.is_empty() {
        str("never")
    } else {
        let fields = fields.iter().map(|f| {
            let (docs, syntax_field) = find_field(syntax, &f.id);
            enclose_space(
                "{",
                docs.append(pp_field(env, f, syntax_field, is_ref)),
                "}",
            )
        });
        strict_concat(fields, " |").nest(INDENT_SPACE)
    }
}

fn pp_opt<'a>(
    env: &'a TypeEnv,
    ty: &'a Type,
    syntax: Option<&'a IDLType>,
    is_ref: bool,
) -> RcDoc<'a> {
    str("[] | ").append(enclose("[", pp_ty_rich(env, ty, syntax, is_ref), "]"))
}

fn pp_function<'a>(env: &'a TypeEnv, func: &'a Function) -> RcDoc<'a> {
    let args = func.args.iter().map(|arg| pp_ty(env, arg, true));
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
        strict_concat([args, rets].into_iter(), ","),
        ">",
    )
}

fn pp_service<'a>(
    env: &'a TypeEnv,
    serv: &'a [(String, Type)],
    syntax: Option<&'a [syntax::Binding]>,
) -> RcDoc<'a> {
    let methods = serv.iter().map(|(id, func)| {
        let mut docs = RcDoc::nil();
        if let Some(bs) = syntax {
            if let Some(b) = bs.iter().find(|b| &b.id == id) {
                docs = pp_docs(&b.docs);
            }
        }
        let func = match func.as_ref() {
            TypeInner::Func(ref func) => pp_function(env, func),
            TypeInner::Var(ref id) => ident(id),
            _ => unreachable!(),
        };
        docs.append(quote_ident(id)).append(kwd(":")).append(func)
    });
    enclose_space("{", concat(methods, ","), "}")
}

fn pp_docs<'a>(docs: &'a [String]) -> RcDoc<'a> {
    if docs.is_empty() {
        RcDoc::nil()
    } else {
        let docs = lines(
            docs.iter()
                .map(|line| RcDoc::text(DOC_COMMENT_LINE_PREFIX).append(line)),
        );
        RcDoc::text(DOC_COMMENT_PREFIX)
            .append(RcDoc::hardline())
            .append(docs)
            .append(RcDoc::text(DOC_COMMENT_SUFFIX))
            .append(RcDoc::hardline())
    }
}

fn pp_defs<'a>(env: &'a TypeEnv, def_list: &'a [&'a str], prog: &'a IDLMergedProg) -> RcDoc<'a> {
    lines(def_list.iter().map(|id| {
        let ty = env.find_type(id).unwrap();
        let syntax = prog.lookup(id);
        let syntax_ty = syntax.map(|s| &s.typ);
        let docs = syntax
            .map(|b| pp_docs(b.docs.as_ref()))
            .unwrap_or(RcDoc::nil());
        let export = match ty.as_ref() {
            TypeInner::Record(_) if !ty.is_tuple() => kwd("export interface")
                .append(ident(id))
                .append(" ")
                .append(pp_ty_rich(env, ty, syntax_ty, false)),
            TypeInner::Service(_) => kwd("export interface")
                .append(ident(id))
                .append(" ")
                .append(pp_ty_rich(env, ty, syntax_ty, false)),
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
                .append(pp_ty_rich(env, ty, syntax_ty, false))
                .append(";"),
        };
        docs.append(export)
    }))
}

fn pp_actor<'a>(env: &'a TypeEnv, ty: &'a Type, syntax: Option<&'a IDLType>) -> RcDoc<'a> {
    let service_doc = kwd("export interface _SERVICE");
    match ty.as_ref() {
        TypeInner::Service(_) => service_doc.append(pp_ty_rich(env, ty, syntax, false)),
        TypeInner::Var(id) => service_doc
            .append(kwd("extends"))
            .append(str(id))
            .append(str(" {}")),
        TypeInner::Class(_, t) => {
            if let Some(IDLType::ClassT(_, syntax_t)) = syntax {
                pp_actor(env, t, Some(syntax_t))
            } else {
                pp_actor(env, t, None)
            }
        }
        _ => unreachable!(),
    }
}

pub fn compile(env: &TypeEnv, actor: &Option<Type>, prog: &IDLMergedProg) -> String {
    let header = r#"import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';
import type { IDL } from '@dfinity/candid';
"#;
    let syntax_actor = prog.resolve_actor().ok().flatten();
    let def_list: Vec<_> = env.0.iter().map(|pair| pair.0.as_ref()).collect();
    let defs = pp_defs(env, &def_list, prog);
    let actor = match actor {
        None => RcDoc::nil(),
        Some(actor) => {
            let docs = syntax_actor
                .as_ref()
                .map(|s| pp_docs(s.docs.as_ref()))
                .unwrap_or(RcDoc::nil());
            docs.append(pp_actor(env, actor, syntax_actor.as_ref().map(|s| &s.typ)))
                .append(RcDoc::line())
                .append("export declare const idlFactory: IDL.InterfaceFactory;")
                .append(RcDoc::line())
                .append("export declare const init: (args: { IDL: typeof IDL }) => IDL.Type[];")
        }
    };
    let doc = RcDoc::text(header)
        .append(RcDoc::line())
        .append(defs)
        .append(actor);
    doc.pretty(LINE_WIDTH).to_string()
}
