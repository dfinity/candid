use super::javascript::is_tuple;
use crate::parser::typing::TypeEnv;
use crate::pretty::*;
use crate::types::{Field, Function, Label, Type};
use pretty::RcDoc;

fn pp_ty(ty: &Type) -> RcDoc {
    use Type::*;
    match *ty {
        Null => str("null"),
        Bool => str("boolean"),
        Nat => str("BigNumber"),
        Int => str("BigNumber"),
        Nat8 => str("number"),
        Nat16 => str("number"),
        Nat32 => str("number"),
        Nat64 => str("BigNumber"),
        Int8 => str("number"),
        Int16 => str("number"),
        Int32 => str("number"),
        Int64 => str("BigNumber"),
        Float32 => str("number"),
        Float64 => str("number"),
        Text => str("string"),
        Reserved => str("any"),
        Empty => str("never"),
        Var(ref s) => str(s),
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
        Func(ref func) => pp_function(func),
        Service(ref serv) => pp_service(serv),
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

fn pp_function(func: &Function) -> RcDoc {
    let args = func
        .args
        .iter()
        .enumerate()
        .map(|(i, ty)| RcDoc::text(format!("arg_{}: ", i)).append(pp_ty(ty)));
    let args = enclose("(", concat(args, ","), ")");
    let rets = str("Promise").append(enclose(
        "<",
        match func.rets.len() {
            0 => str("undefined"),
            1 => pp_ty(&func.rets[0]),
            _ => enclose("[", concat(func.args.iter().map(pp_ty), ","), "]"),
        },
        ">",
    ));
    args.append(" => ").append(rets).nest(INDENT_SPACE)
}

fn pp_service(serv: &[(String, Type)]) -> RcDoc {
    let doc = concat(
        serv.iter()
            .map(|(id, func)| quote_ident(id).append(kwd(":")).append(pp_ty(func))),
        ",",
    );
    enclose_space("{", doc, "}")
}

fn pp_defs<'a>(env: &'a TypeEnv, def_list: &'a [&'a str]) -> RcDoc<'a> {
    lines(def_list.iter().map(|id| {
        let ty = env.find_type(id).unwrap();
        kwd("export type")
            .append(ident(id))
            .append(kwd("="))
            .append(pp_ty(ty))
            .append(";")
    }))
}

fn pp_actor(ty: &Type) -> RcDoc {
    match ty {
        Type::Service(_) => kwd("export interface SERVICE").append(pp_ty(ty)),
        Type::Var(id) => kwd("export type SERVICE =").append(str(id)),
        Type::Class(_, t) => pp_actor(t),
        _ => unreachable!(),
    }
}

pub fn compile(env: &TypeEnv, actor: &Option<Type>) -> String {
    let header = r#"// AUTO-GENERATED. DO NOT EDIT.
import { Principal } from '@dfinity/agent';
import BigNumber from 'bignumber.js';
"#;
    let def_list: Vec<_> = env.0.iter().map(|pair| pair.0.as_ref()).collect();
    let defs = pp_defs(env, &def_list);
    let actor = match actor {
        None => RcDoc::nil(),
        Some(actor) => pp_actor(actor).append(";"),
    };
    let doc = RcDoc::text(header).append(defs).append(actor);
    doc.pretty(LINE_WIDTH).to_string()
}
