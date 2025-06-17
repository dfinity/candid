// This module implements the Candid to Motoko binding as specified in
// https://github.com/dfinity/motoko/blob/master/design/IDL-Motoko.md

use candid::pretty::candid::is_valid_as_id;
use candid::pretty::utils::*;
use candid::types::{ArgType, Field, FuncMode, Function, Label, SharedLabel, Type, TypeInner};
use candid::TypeEnv;
use pretty::RcDoc;

// The definition of tuple is language specific.
fn is_tuple(t: &Type) -> bool {
    match t.as_ref() {
        TypeInner::Record(ref fs) => {
            if fs.len() <= 1 {
                return false;
            }
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
static KEYWORDS: [&str; 48] = [
    "actor",
    "and",
    "async",
    "async*",
    "assert",
    "await",
    "await*",
    "break",
    "case",
    "catch",
    "class",
    "continue",
    "composite",
    "debug",
    "debug_show",
    "else",
    "false",
    "flexible",
    "for",
    "from_candid",
    "func",
    "if",
    "in",
    "import",
    "module",
    "not",
    "null",
    "object",
    "or",
    "label",
    "let",
    "loop",
    "private",
    "public",
    "query",
    "return",
    "shared",
    "stable",
    "switch",
    "system",
    "try",
    "throw",
    "to_candid",
    "true",
    "type",
    "var",
    "while",
    "with",
];
fn escape(id: &str, is_method: bool) -> RcDoc {
    if KEYWORDS.contains(&id) {
        str(id).append("_")
    } else if is_valid_as_id(id) {
        if id.ends_with('_') {
            str(id).append("_")
        } else {
            str(id)
        }
    } else if !is_method {
        str("_")
            .append(candid::idl_hash(id).to_string())
            .append("_")
    } else {
        panic!("Candid method {id} is not a valid Motoko id");
    }
}

fn pp_ty(ty: &Type) -> RcDoc {
    use TypeInner::*;
    match ty.as_ref() {
        Null => str("Null"),
        Bool => str("Bool"),
        Nat => str("Nat"),
        Int => str("Int"),
        Nat8 => str("Nat8"),
        Nat16 => str("Nat16"),
        Nat32 => str("Nat32"),
        Nat64 => str("Nat64"),
        Int8 => str("Int8"),
        Int16 => str("Int16"),
        Int32 => str("Int32"),
        Int64 => str("Int64"),
        Float32 => panic!("float32 not supported in Motoko"),
        Float64 => str("Float"),
        Text => str("Text"),
        Reserved => str("Any"),
        Empty => str("None"),
        Var(ref s) => escape(s, false),
        Principal => str("Principal"),
        Opt(ref t) => str("?").append(pp_ty(t)),
        Vec(ref t) if matches!(t.as_ref(), Nat8) => str("Blob"),
        Vec(ref t) => enclose("[", pp_ty(t), "]"),
        Record(ref fs) => {
            if is_tuple(ty) {
                let tuple = concat(fs.iter().map(|f| pp_ty(&f.ty)), ",");
                enclose("(", tuple, ")")
            } else {
                let fields = concat(fs.iter().map(pp_field), ";");
                enclose_space("{", fields, "}")
            }
        }
        Variant(ref fs) => {
            if fs.is_empty() {
                str("{#}")
            } else {
                let fields = concat(fs.iter().map(pp_variant), ";");
                enclose_space("{", fields, "}")
            }
        }
        Func(ref func) => pp_function(func),
        Service(ref serv) => pp_service(serv),
        Class(ref args, ref t) => {
            let doc = pp_args(args).append(" -> async ");
            match t.as_ref() {
                Service(ref serv) => doc.append(pp_service(serv)),
                Var(ref s) => doc.append(s),
                _ => unreachable!(),
            }
        }
        Knot(_) | Unknown | Future => unreachable!(),
    }
}

fn pp_label(id: &SharedLabel) -> RcDoc {
    match &**id {
        Label::Named(str) => escape(str, false),
        Label::Id(n) | Label::Unnamed(n) => str("_")
            .append(RcDoc::as_string(n))
            .append("_")
            .append(RcDoc::space()),
    }
}

fn pp_field(field: &Field) -> RcDoc {
    pp_label(&field.id).append(" : ").append(pp_ty(&field.ty))
}
fn pp_variant(field: &Field) -> RcDoc {
    let doc = str("#").append(pp_label(&field.id));
    if *field.ty != TypeInner::Null {
        doc.append(" : ").append(pp_ty(&field.ty))
    } else {
        doc
    }
}

fn pp_function(func: &Function) -> RcDoc {
    let args = pp_args(&func.args);
    let rets = pp_rets(&func.rets);
    match func.modes.as_slice() {
        [FuncMode::Oneway] => kwd("shared").append(args).append(" -> ").append("()"),
        [FuncMode::Query] => kwd("shared query")
            .append(args)
            .append(" -> ")
            .append("async ")
            .append(rets),
        [FuncMode::CompositeQuery] => kwd("shared composite query")
            .append(args)
            .append(" -> ")
            .append("async ")
            .append(rets),
        [] => kwd("shared")
            .append(args)
            .append(" -> ")
            .append("async ")
            .append(rets),
        _ => unreachable!(),
    }
    .nest(INDENT_SPACE)
}
fn pp_args(args: &[ArgType]) -> RcDoc {
    match args {
        [ty] => {
            let typ = if is_tuple(&ty.typ) {
                enclose("(", pp_ty(&ty.typ), ")")
            } else {
                pp_ty(&ty.typ)
            };
            if let Some(name) = &ty.name {
                enclose("(", escape(name, false).append(" : ").append(typ), ")")
            } else {
                typ
            }
        }
        _ => {
            let args = args.iter().map(|arg| {
                if let Some(name) = &arg.name {
                    escape(name, false).append(" : ").append(pp_ty(&arg.typ))
                } else {
                    pp_ty(&arg.typ)
                }
            });
            let doc = concat(args, ",");
            enclose("(", doc, ")")
        }
    }
}

fn pp_rets(args: &[Type]) -> RcDoc {
    match args {
        [ty] => {
            if is_tuple(ty) {
                enclose("(", pp_ty(ty), ")")
            } else {
                pp_ty(ty)
            }
        }
        _ => {
            let doc = concat(args.iter().map(pp_ty), ",");
            enclose("(", doc, ")")
        }
    }
}

fn pp_service(serv: &[(String, Type)]) -> RcDoc {
    let doc = concat(
        serv.iter()
            .map(|(id, func)| escape(id, true).append(" : ").append(pp_ty(func))),
        ";",
    );
    kwd("actor").append(enclose_space("{", doc, "}"))
}

fn pp_defs(env: &TypeEnv) -> RcDoc {
    lines(env.0.iter().map(|(id, ty)| {
        kwd("public type")
            .append(escape(id, false))
            .append(" = ")
            .append(pp_ty(ty))
            .append(";")
    }))
}

fn pp_actor(ty: &Type) -> RcDoc {
    match ty.as_ref() {
        TypeInner::Service(ref serv) => pp_service(serv),
        TypeInner::Var(_) | TypeInner::Class(_, _) => pp_ty(ty),
        _ => unreachable!(),
    }
}

pub fn compile(env: &TypeEnv, actor: &Option<Type>) -> String {
    let header = r#"// This is a generated Motoko binding.
// Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.
"#;
    let doc = match actor {
        None => pp_defs(env),
        Some(actor) => {
            let defs = pp_defs(env);
            let actor = kwd("public type Self =").append(pp_actor(actor));
            defs.append(actor)
        }
    };
    RcDoc::text(header)
        .append(RcDoc::line())
        .append("module ")
        .append(enclose_space("{", doc, "}"))
        .pretty(LINE_WIDTH)
        .to_string()
}
