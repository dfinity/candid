// This module implements the Candid to Motoko binding as specified in
// https://github.com/dfinity/motoko/blob/master/design/IDL-Motoko.md

use candid::pretty::candid::is_valid_as_id;
use candid::pretty::utils::*;
use candid::types::{
    syntax::{Binding, FuncType, IDLArgType, IDLEnv, IDLType, PrimType, TypeField},
    FuncMode, Label,
};
use pretty::RcDoc;

fn is_tuple(t: &IDLType) -> bool {
    match t {
        IDLType::RecordT(ref fs) => {
            if fs.len() <= 1 {
                return false;
            }
            t.is_tuple()
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

fn pp_prim_ty(prim: &PrimType) -> RcDoc {
    use PrimType::*;
    match prim {
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
    }
}

fn pp_ty(ty: &IDLType) -> RcDoc {
    use IDLType::*;
    match ty {
        PrimT(prim) => pp_prim_ty(prim),
        VarT(ref s) => escape(s, false),
        PrincipalT => str("Principal"),
        OptT(ref t) => str("?").append(pp_ty(t)),
        VecT(ref t) if matches!(t.as_ref(), PrimT(PrimType::Nat8)) => str("Blob"),
        VecT(ref t) => enclose("[", pp_ty(t), "]"),
        RecordT(ref fs) => {
            if is_tuple(ty) {
                let tuple = concat(fs.iter().map(|f| pp_ty(&f.typ)), ",");
                enclose("(", tuple, ")")
            } else {
                let fields = concat(fs.iter().map(pp_field), ";");
                enclose_space("{", fields, "}")
            }
        }
        VariantT(ref fs) => {
            if fs.is_empty() {
                str("{#}")
            } else {
                let fields = concat(fs.iter().map(pp_variant), ";");
                enclose_space("{", fields, "}")
            }
        }
        FuncT(ref func) => pp_function(func),
        ServT(ref serv) => pp_service(serv),
        ClassT(ref args, ref t) => {
            let doc = pp_args(args).append(" -> async ");
            match t.as_ref() {
                IDLType::ServT(ref serv) => doc.append(pp_service(serv)),
                IDLType::VarT(ref s) => doc.append(s),
                _ => unreachable!(),
            }
        }
        KnotT(_) => unreachable!(),
    }
}

fn pp_label(id: &Label) -> RcDoc {
    match id {
        Label::Named(str) => escape(str, false),
        Label::Id(n) | Label::Unnamed(n) => str("_")
            .append(RcDoc::as_string(n))
            .append("_")
            .append(RcDoc::space()),
    }
}

fn pp_field(field: &TypeField) -> RcDoc {
    pp_label(&field.label)
        .append(" : ")
        .append(pp_ty(&field.typ))
}
fn pp_variant(field: &TypeField) -> RcDoc {
    let doc = str("#").append(pp_label(&field.label));
    if !field.typ.is_null() {
        doc.append(" : ").append(pp_ty(&field.typ))
    } else {
        doc
    }
}

fn pp_function(func: &FuncType) -> RcDoc {
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
fn pp_args(args: &[IDLArgType]) -> RcDoc {
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

fn pp_rets(args: &[IDLType]) -> RcDoc {
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

fn pp_service(serv: &[Binding]) -> RcDoc {
    let doc = concat(
        serv.iter()
            .map(|b| escape(&b.id, true).append(" : ").append(pp_ty(&b.typ))),
        ";",
    );
    kwd("actor").append(enclose_space("{", doc, "}"))
}

fn pp_defs<'a>(bindings: &[(&'a str, &'a IDLType)]) -> RcDoc<'a> {
    lines(bindings.iter().map(|(id, typ)| {
        kwd("public type")
            .append(escape(id, false))
            .append(" = ")
            .append(pp_ty(typ))
            .append(";")
    }))
}

fn pp_actor(ty: &IDLType) -> RcDoc {
    match ty {
        IDLType::ServT(ref serv) => pp_service(serv),
        IDLType::VarT(_) | IDLType::ClassT(_, _) => pp_ty(ty),
        _ => unreachable!(),
    }
}

pub fn compile(env: &IDLEnv) -> String {
    let header = r#"// This is a generated Motoko binding.
// Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.
"#;
    let bindings = env.get_bindings();
    let doc = match &env.actor {
        None => pp_defs(&bindings),
        Some(actor) => {
            let defs = pp_defs(&bindings);
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
