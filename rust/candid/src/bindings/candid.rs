use crate::parser::typing::TypeEnv;
use crate::pretty::*;
use crate::types::{Field, Function, Label, Type};
use pretty::RcDoc;

static KEYWORDS: [&str; 29] = [
    "import",
    "service",
    "func",
    "type",
    "opt",
    "vec",
    "record",
    "variant",
    "blob",
    "principal",
    "nat",
    "nat8",
    "nat16",
    "nat32",
    "nat64",
    "int",
    "int8",
    "int16",
    "int32",
    "int64",
    "float32",
    "float64",
    "bool",
    "text",
    "null",
    "reserved",
    "empty",
    "oneway",
    "query",
];

fn is_keyword(id: &str) -> bool {
    KEYWORDS.contains(&id)
}

pub(crate) fn is_valid_as_id(id: &str) -> bool {
    if id.is_empty() || !id.is_ascii() {
        return false;
    }
    for (i, c) in id.char_indices() {
        if i == 0 {
            if !c.is_ascii_alphabetic() && c != '_' {
                return false;
            }
        } else if !c.is_ascii_alphanumeric() && c != '_' {
            return false;
        }
    }
    true
}

fn needs_quote(id: &str) -> bool {
    !is_valid_as_id(id) || is_keyword(id)
}

pub(crate) fn ident_string(id: &str) -> String {
    if needs_quote(id) {
        format!("\"{}\"", id.escape_debug())
    } else {
        id.to_string()
    }
}

fn pp_text(id: &str) -> RcDoc {
    RcDoc::text(ident_string(id))
}

pub fn pp_ty(ty: &Type) -> RcDoc {
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
            if ty.is_tuple() {
                let tuple = concat(fs.iter().map(|f| pp_ty(&f.ty)), ";");
                kwd("record").append(enclose_space("{", tuple, "}"))
            } else {
                kwd("record").append(pp_fields(fs, false))
            }
        }
        Variant(ref fs) => kwd("variant").append(pp_fields(fs, true)),
        Func(ref func) => kwd("func").append(pp_function(func)),
        Service(ref serv) => kwd("service").append(pp_service(serv)),
        Class(ref args, ref t) => {
            let doc = pp_args(&args).append(" ->").append(RcDoc::space());
            match t.as_ref() {
                Service(ref serv) => doc.append(pp_service(serv)),
                Var(ref s) => doc.append(s),
                _ => unreachable!(),
            }
        }
        Knot(ref id) => RcDoc::text(format!("{}", id)),
        Unknown => str("unknown"),
    }
}

pub fn pp_label(id: &Label) -> RcDoc {
    match id {
        Label::Named(id) => pp_text(id),
        Label::Id(_) | Label::Unnamed(_) => RcDoc::as_string(id),
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

pub fn pp_function(func: &Function) -> RcDoc {
    let args = pp_args(&func.args);
    let rets = pp_args(&func.rets);
    let modes = pp_modes(&func.modes);
    args.append(" ->")
        .append(RcDoc::space())
        .append(rets.append(modes))
        .nest(INDENT_SPACE)
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
            pp_text(id).append(kwd(" :")).append(func_doc)
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
    match ty {
        Type::Service(ref serv) => pp_service(serv),
        Type::Var(_) | Type::Class(_, _) => pp_ty(ty),
        _ => unreachable!(),
    }
}

pub fn compile(env: &TypeEnv, actor: &Option<Type>) -> String {
    match actor {
        None => pp_defs(env).pretty(LINE_WIDTH).to_string(),
        Some(actor) => {
            let defs = pp_defs(env);
            let actor = kwd("service :").append(pp_actor(actor));
            let doc = defs.append(actor);
            doc.pretty(LINE_WIDTH).to_string()
        }
    }
}
