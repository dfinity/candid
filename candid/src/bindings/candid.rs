use crate::parser::typing::TypeEnv;
use crate::pretty::*;
use crate::types::{Field, Function, Label, Type};
use pretty::RcDoc;

// The definition of tuple is language specific.
fn is_tuple(t: &Type) -> bool {
    match t {
        Type::Record(ref fs) => {
            for (i, field) in fs.iter().enumerate() {
                if field.id.get_id() != (i as u32) {
                    return false;
                }
            }
            true
        }
        _ => false,
    }
}

fn pp_ty(ty: &Type) -> RcDoc {
    use Type::*;
    match *ty {
        Null => str("null"),
        Bool => str("bool"),
        Nat => str("nat"),
        Int => str("int"),
        Nat8 => str("nat8"),
        Nat16 => str("nat16"),
        Nat32 => str("nat32"),
        Nat64 => str("nat64"),
        Int8 => str("int8"),
        Int16 => str("int16"),
        Int32 => str("int32"),
        Int64 => str("int64"),
        Float32 => str("float32"),
        Float64 => str("float64"),
        Text => str("text"),
        Reserved => str("reserved"),
        Empty => str("empty"),
        Var(ref s) => str(s),
        Principal => str("principal"),
        Opt(ref t) => kwd("opt").append(pp_ty(t)),
        Vec(ref t) => kwd("vec").append(pp_ty(t)),
        Record(ref fs) => {
            if is_tuple(ty) {
                let tuple = concat(fs.iter().map(|f| pp_ty(&f.ty)), ";");
                kwd("record").append(enclose_space("{", tuple, "}"))
            } else {
                kwd("record").append(pp_fields(fs, false))
            }
        }
        Variant(ref fs) => kwd("variant").append(pp_fields(fs, true)),
        Func(ref func) => kwd("func").append(pp_function(func)),
        Service(ref serv) => kwd("service").append(pp_service(serv)),
        _ => unreachable!(),
    }
}

fn pp_label(id: &Label) -> RcDoc {
    match id {
        Label::Named(id) => str("\"")
            .append(format!("{}", id.escape_debug()))
            .append("\""),
        Label::Id(n) | Label::Unnamed(n) => RcDoc::as_string(n),
    }
}

fn pp_field(field: &Field, is_variant: bool) -> RcDoc {
    let ty_doc = if is_variant && field.ty == Type::Null {
        RcDoc::nil()
    } else {
        kwd(" :").append(pp_ty(&field.ty))
    };
    pp_label(&field.id).append(ty_doc)
}

fn pp_fields(fs: &[Field], is_variant: bool) -> RcDoc {
    let fields = concat(fs.iter().map(|f| pp_field(f, is_variant)), ";");
    enclose_space("{", fields, "}")
}

fn pp_function(func: &Function) -> RcDoc {
    let args = pp_args(&func.args);
    let rets = pp_args(&func.rets);
    let modes = pp_modes(&func.modes);
    args.append(" ->")
        .nest(INDENT_SPACE)
        .append(RcDoc::softline())
        .append(rets)
        .append(modes)
        .group()
}

fn pp_args(args: &[Type]) -> RcDoc {
    let doc = concat(args.iter().map(pp_ty), ",");
    enclose("(", doc, ")")
}

fn pp_modes(modes: &[crate::parser::types::FuncMode]) -> RcDoc {
    RcDoc::concat(modes.iter().map(|m| RcDoc::space().append(m.to_doc())))
}

fn pp_service(serv: &[(String, Type)]) -> RcDoc {
    let doc = concat(
        serv.iter().map(|(id, func)| {
            let func_doc = match func {
                Type::Func(ref f) => pp_function(f),
                Type::Var(_) => pp_ty(func),
                _ => unreachable!(),
            };
            doublequote_ident(id).append(kwd(":")).append(func_doc)
        }),
        ";",
    );
    enclose_space("{", doc, "}")
}

fn pp_defs(env: &TypeEnv) -> RcDoc {
    lines(env.0.iter().map(|(id, ty)| {
        kwd("type")
            .append(ident(id))
            .append(kwd("="))
            .append(pp_ty(ty))
            .append(";")
    }))
}

fn pp_actor(ty: &Type) -> RcDoc {
    let doc = match ty {
        Type::Service(ref serv) => pp_service(serv),
        Type::Var(_) => pp_ty(ty),
        _ => unreachable!(),
    };
    kwd("service :").append(doc)
}

pub fn compile(env: &TypeEnv, actor: &Option<Type>) -> String {
    match actor {
        None => "".to_string(),
        Some(actor) => {
            let defs = pp_defs(env);
            let actor = pp_actor(actor);
            let doc = defs.append(actor);
            doc.pretty(LINE_WIDTH).to_string()
        }
    }
}
