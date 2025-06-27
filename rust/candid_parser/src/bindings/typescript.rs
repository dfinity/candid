use super::javascript::{ident, is_tuple};
use candid::pretty::utils::*;
use candid::types::{
    syntax::{Binding, FuncType, IDLMergedProg, IDLType, PrimType, TypeField},
    Label,
};
use pretty::RcDoc;

fn pp_prim_ty(ty: &PrimType) -> RcDoc {
    use PrimType::*;
    match ty {
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
    }
}

fn pp_ty<'a>(prog: &'a IDLMergedProg, ty: &'a IDLType, is_ref: bool) -> RcDoc<'a> {
    use IDLType::*;
    match ty {
        PrimT(ref ty) => pp_prim_ty(ty),
        VarT(ref id) => {
            let ty = prog.rec_find_type(id).unwrap();
            if matches!(ty, FuncT(_)) {
                return pp_inline_func();
            }
            if is_ref && matches!(ty, ServT(_)) {
                return pp_inline_service();
            }
            ident(id)
        }
        PrincipalT => str("Principal"),
        OptT(ref t) => str("[] | ").append(enclose("[", pp_ty(prog, t, is_ref), "]")),
        VecT(ref t) => {
            let ty = match t.as_ref() {
                VarT(ref id) => {
                    let ty = prog.rec_find_type(id).unwrap();
                    if matches!(
                        ty,
                        PrimT(PrimType::Nat8)
                            | PrimT(PrimType::Nat16)
                            | PrimT(PrimType::Nat32)
                            | PrimT(PrimType::Nat64)
                            | PrimT(PrimType::Int8)
                            | PrimT(PrimType::Int16)
                            | PrimT(PrimType::Int32)
                            | PrimT(PrimType::Int64)
                    ) {
                        ty
                    } else {
                        t
                    }
                }
                _ => t,
            };
            match ty {
                PrimT(PrimType::Nat8) => str("Uint8Array | number[]"),
                PrimT(PrimType::Nat16) => str("Uint16Array | number[]"),
                PrimT(PrimType::Nat32) => str("Uint32Array | number[]"),
                PrimT(PrimType::Nat64) => str("BigUint64Array | bigint[]"),
                PrimT(PrimType::Int8) => str("Int8Array | number[]"),
                PrimT(PrimType::Int16) => str("Int16Array | number[]"),
                PrimT(PrimType::Int32) => str("Int32Array | number[]"),
                PrimT(PrimType::Int64) => str("BigInt64Array | bigint[]"),
                _ => str("Array").append(enclose("<", pp_ty(prog, t, is_ref), ">")),
            }
        }
        RecordT(ref fs) => {
            if is_tuple(ty) {
                let tuple = concat(fs.iter().map(|f| pp_ty(prog, &f.typ, is_ref)), ",");
                enclose("[", tuple, "]")
            } else {
                let fields = concat(fs.iter().map(|f| pp_field(prog, f, is_ref)), ",");
                enclose_space("{", fields, "}")
            }
        }
        VariantT(ref fs) => {
            if fs.is_empty() {
                str("never")
            } else {
                strict_concat(
                    fs.iter()
                        .map(|f| enclose_space("{", pp_field(prog, f, is_ref), "}")),
                    " |",
                )
                .nest(INDENT_SPACE)
            }
        }
        FuncT(_) => pp_inline_func(),
        ServT(_) => pp_inline_service(),
        ClassT(_, _) | FutureT | UnknownT => unreachable!(),
    }
}

fn pp_inline_func<'a>() -> RcDoc<'a> {
    str("[Principal, string]")
}

fn pp_inline_service<'a>() -> RcDoc<'a> {
    str("Principal")
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

fn pp_field<'a>(prog: &'a IDLMergedProg, field: &'a TypeField, is_ref: bool) -> RcDoc<'a> {
    pp_label(&field.label)
        .append(kwd(":"))
        .append(pp_ty(prog, &field.typ, is_ref))
}

fn pp_function<'a>(prog: &'a IDLMergedProg, func: &'a FuncType) -> RcDoc<'a> {
    let args = func.args.iter().map(|arg| pp_ty(prog, &arg.typ, true));
    let args = enclose("[", concat(args, ","), "]");
    let rets = match func.rets.len() {
        0 => str("undefined"),
        1 => pp_ty(prog, &func.rets[0], true),
        _ => enclose(
            "[",
            concat(func.rets.iter().map(|ty| pp_ty(prog, ty, true)), ","),
            "]",
        ),
    };
    enclose(
        "ActorMethod<",
        strict_concat([args, rets].iter().cloned(), ","),
        ">",
    )
}

fn pp_service<'a>(prog: &'a IDLMergedProg, serv: &'a [Binding]) -> RcDoc<'a> {
    let doc = concat(
        serv.iter().map(|Binding { id, typ }| {
            let func = match typ {
                IDLType::FuncT(ref func) => pp_function(prog, func),
                IDLType::VarT(ref id) => ident(id),
                _ => unreachable!(),
            };
            quote_ident(id).append(kwd(":")).append(func)
        }),
        ",",
    );
    enclose_space("{", doc, "}")
}

fn pp_defs<'a>(prog: &'a IDLMergedProg, def_list: &'a [&'a str]) -> RcDoc<'a> {
    lines(def_list.iter().map(|id| {
        let ty = prog.find_type(id).unwrap();
        let export = match ty {
            IDLType::RecordT(_) if !ty.is_tuple() => kwd("export interface")
                .append(ident(id))
                .append(" ")
                .append(pp_ty(prog, ty, false)),
            IDLType::ServT(ref serv) => kwd("export interface")
                .append(ident(id))
                .append(" ")
                .append(pp_service(prog, serv)),
            IDLType::FuncT(ref func) => kwd("export type")
                .append(ident(id))
                .append(" = ")
                .append(pp_function(prog, func))
                .append(";"),
            IDLType::VarT(ref inner_id) => kwd("export type")
                .append(ident(id))
                .append(" = ")
                .append(ident(inner_id))
                .append(";"),
            _ => kwd("export type")
                .append(ident(id))
                .append(" = ")
                .append(pp_ty(prog, ty, false))
                .append(";"),
        };
        export
    }))
}

fn pp_actor<'a>(prog: &'a IDLMergedProg, ty: &'a IDLType) -> RcDoc<'a> {
    match ty {
        IDLType::ServT(ref serv) => kwd("export interface _SERVICE").append(pp_service(prog, serv)),
        IDLType::VarT(id) => kwd("export interface _SERVICE extends")
            .append(str(id))
            .append(str(" {}")),
        IDLType::ClassT(_, t) => pp_actor(prog, t),
        _ => unreachable!(),
    }
}

pub fn compile(prog: &IDLMergedProg) -> String {
    let header = r#"import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';
import type { IDL } from '@dfinity/candid';
"#;
    let def_list = prog.types_ids();
    let defs = pp_defs(prog, &def_list);
    let actor = match &prog.actor {
        None => RcDoc::nil(),
        Some(actor) => pp_actor(prog, actor)
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
