// This module implements the Candid to Motoko binding as specified in
// https://github.com/dfinity/motoko/blob/master/design/IDL-Motoko.md

use crate::syntax::{self, IDLActorType, IDLMergedProg, IDLType};
use candid::pretty::candid::is_valid_as_id;
use candid::pretty::utils::*;
use candid::types::{Field, FuncMode, Function, Label, SharedLabel, Type, TypeInner};
use candid::TypeEnv;
use pretty::RcDoc;

// The definition of tuple is language specific.
fn is_tuple(t: &Type) -> bool {
    match t.as_ref() {
        TypeInner::Record(ref fs) => is_tuple_fields(fs),
        _ => false,
    }
}

fn is_tuple_fields(fs: &[Field]) -> bool {
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
fn escape_str(id: &str) -> String {
    if KEYWORDS.contains(&id) || (is_valid_as_id(id) && id.ends_with('_')) {
        format!("{id}_")
    } else if is_valid_as_id(id) {
        id.to_string()
    } else {
        format!("_{}_", candid::idl_hash(id))
    }
}

fn escape(id: &str, is_method: bool) -> RcDoc<'_> {
    if is_method && !KEYWORDS.contains(&id) && !is_valid_as_id(id) {
        panic!("Candid method {id} is not a valid Motoko id");
    }
    RcDoc::text(escape_str(id))
}

fn to_upper_camel_case(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut capitalize = true;
    for c in s.chars() {
        // '_' is the standard Candid separator; '-' is included defensively
        if c == '_' || c == '-' {
            capitalize = true;
        } else if capitalize {
            out.extend(c.to_uppercase());
            capitalize = false;
        } else {
            out.push(c);
        }
    }
    out
}

// Returns the UpperCamelCase display name for a type alias, falling back to the
// original escaped name when:
//   - the transform produces an empty string (e.g. id = "_"),
//   - the result would collide with another alias in env, or
//   - the result is "Self" (always reserved: pp_actor emits it when an actor is
//     present, and being conservative here avoids surprises if a file is later
//     extended with a service declaration).
fn type_display_name(env: &TypeEnv, id: &str) -> String {
    let camel = to_upper_camel_case(id);
    let collision = camel.is_empty()
        || camel == "Self"
        || env.0.keys().any(|k| k != id && to_upper_camel_case(k) == camel);
    if collision {
        let fallback = escape_str(id);
        // escape_str doesn't know about "Self" being reserved, so guard explicitly.
        if fallback == "Self" {
            format!("{fallback}_")
        } else {
            fallback
        }
    } else {
        camel
    }
}

fn pp_ty_rich<'a>(env: &'a TypeEnv, ty: &'a Type, syntax: Option<&'a IDLType>) -> RcDoc<'a> {
    match (ty.as_ref(), syntax) {
        (TypeInner::Service(ref meths), Some(IDLType::ServT(methods))) => {
            pp_service(env, meths, Some(methods))
        }
        (TypeInner::Class(ref args, t), Some(IDLType::ClassT(_, syntax_t))) => {
            pp_class(env, (args, t), Some(syntax_t))
        }
        (TypeInner::Record(ref fields), Some(IDLType::RecordT(syntax_fields))) => {
            pp_record(env, fields, Some(syntax_fields))
        }
        (TypeInner::Variant(ref fields), Some(IDLType::VariantT(syntax_fields))) => {
            pp_variant(env, fields, Some(syntax_fields))
        }
        (TypeInner::Opt(ref inner), Some(IDLType::OptT(syntax))) => {
            str("?").append(pp_ty_rich(env, inner, Some(syntax)))
        }
        (TypeInner::Vec(ref inner), Some(IDLType::VecT(syntax))) => pp_vec(env, inner, Some(syntax)),
        (_, _) => pp_ty(env, ty),
    }
}

fn pp_ty<'a>(env: &'a TypeEnv, ty: &'a Type) -> RcDoc<'a> {
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
        Float32 => str("Float32"),
        Float64 => str("Float"),
        Text => str("Text"),
        Reserved => str("Any"),
        Empty => str("None"),
        Var(ref s) => RcDoc::text(type_display_name(env, s)),
        Principal => str("Principal"),
        Opt(ref t) => str("?").append(pp_ty(env, t)),
        Vec(ref t) => pp_vec(env, t, None),
        Record(ref fs) => pp_record(env, fs, None),
        Variant(ref fs) => pp_variant(env, fs, None),
        Func(ref func) => pp_function(env, func),
        Service(ref serv) => pp_service(env, serv, None),
        Class(ref args, ref t) => pp_class(env, (args, t), None),
        Knot(_) | Unknown | Future => unreachable!(),
    }
}

fn pp_label(id: &SharedLabel) -> RcDoc<'_> {
    match &**id {
        Label::Named(str) => escape(str, false),
        Label::Id(n) | Label::Unnamed(n) => str("_")
            .append(RcDoc::as_string(n))
            .append("_")
            .append(RcDoc::space()),
    }
}

fn pp_function<'a>(env: &'a TypeEnv, func: &'a Function) -> RcDoc<'a> {
    let args = pp_args(env, &func.args);
    let rets = pp_rets(env, &func.rets);
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
fn pp_args<'a>(env: &'a TypeEnv, args: &'a [Type]) -> RcDoc<'a> {
    match args {
        [ty] => {
            if is_tuple(ty) {
                enclose("(", pp_ty(env, ty), ")")
            } else {
                pp_ty(env, ty)
            }
        }
        _ => {
            let doc = concat(args.iter().map(|ty| pp_ty(env, ty)), ",");
            enclose("(", doc, ")")
        }
    }
}

fn pp_rets<'a>(env: &'a TypeEnv, args: &'a [Type]) -> RcDoc<'a> {
    pp_args(env, args)
}

fn pp_service<'a>(env: &'a TypeEnv, serv: &'a [(String, Type)], syntax: Option<&'a [syntax::Binding]>) -> RcDoc<'a> {
    let methods = serv.iter().map(|(id, func)| {
        let mut docs = RcDoc::nil();
        let mut syntax_field_ty = None;
        if let Some(bs) = syntax {
            if let Some(b) = bs.iter().find(|b| &b.id == id) {
                docs = pp_docs(&b.docs);
                syntax_field_ty = Some(&b.typ)
            }
        }
        docs.append(escape(id, true))
            .append(" : ")
            .append(pp_ty_rich(env, func, syntax_field_ty))
    });
    kwd("actor").append(enclose_space("{", concat(methods, ";"), "}"))
}

fn pp_tuple<'a>(env: &'a TypeEnv, fields: &'a [Field]) -> RcDoc<'a> {
    let tuple = concat(fields.iter().map(|f| pp_ty(env, &f.ty)), ",");
    enclose("(", tuple, ")")
}

fn pp_vec<'a>(env: &'a TypeEnv, inner: &'a Type, syntax: Option<&'a IDLType>) -> RcDoc<'a> {
    if matches!(inner.as_ref(), TypeInner::Nat8) {
        str("Blob")
    } else {
        enclose("[", pp_ty_rich(env, inner, syntax), "]")
    }
}

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

fn pp_record<'a>(env: &'a TypeEnv, fields: &'a [Field], syntax: Option<&'a [syntax::TypeField]>) -> RcDoc<'a> {
    if is_tuple_fields(fields) {
        return pp_tuple(env, fields);
    }
    let fields = fields.iter().map(|field| {
        let (docs, syntax_field) = find_field(syntax, &field.id);
        docs.append(pp_label(&field.id))
            .append(" : ")
            .append(pp_ty_rich(env, &field.ty, syntax_field))
    });
    enclose_space("{", concat(fields, ";"), "}")
}

fn pp_variant<'a>(env: &'a TypeEnv, fields: &'a [Field], syntax: Option<&'a [syntax::TypeField]>) -> RcDoc<'a> {
    if fields.is_empty() {
        return str("{#}");
    }
    let fields = fields.iter().map(|field| {
        let (docs, syntax_field) = find_field(syntax, &field.id);
        let doc = docs.append(str("#")).append(pp_label(&field.id));
        if *field.ty != TypeInner::Null {
            doc.append(" : ")
                .append(pp_ty_rich(env, &field.ty, syntax_field))
        } else {
            doc
        }
    });
    enclose_space("{", concat(fields, ";"), "}")
}

fn pp_class<'a>(env: &'a TypeEnv, (args, ty): (&'a [Type], &'a Type), syntax: Option<&'a IDLType>) -> RcDoc<'a> {
    let doc = pp_args(env, args).append(" -> async ");
    match ty.as_ref() {
        TypeInner::Service(_) => doc.append(pp_ty_rich(env, ty, syntax)),
        TypeInner::Var(_) => doc.append(pp_ty(env, ty)),
        _ => unreachable!(),
    }
}

fn pp_docs<'a>(docs: &'a [String]) -> RcDoc<'a> {
    lines(docs.iter().map(|line| RcDoc::text("/// ").append(line)))
}

fn pp_defs<'a>(env: &'a TypeEnv, prog: &'a IDLMergedProg) -> RcDoc<'a> {
    lines(env.0.iter().map(|(id, ty)| {
        let syntax = prog.lookup(id);
        let docs = syntax
            .map(|b| pp_docs(b.docs.as_ref()))
            .unwrap_or(RcDoc::nil());
        docs.append(kwd("public type"))
            .append(RcDoc::text(type_display_name(env, id)))
            .append(" = ")
            .append(pp_ty_rich(env, ty, syntax.map(|b| &b.typ)))
            .append(";")
    }))
}

fn pp_actor<'a>(env: &'a TypeEnv, ty: &'a Type, syntax: Option<&'a IDLActorType>) -> RcDoc<'a> {
    let self_doc = kwd("public type Self =");
    match ty.as_ref() {
        TypeInner::Service(ref serv) => match syntax {
            Some(IDLActorType {
                typ: IDLType::ServT(ref fields),
                docs,
            }) => {
                let docs = pp_docs(docs);
                docs.append(self_doc).append(pp_service(env, serv, Some(fields)))
            }
            _ => pp_service(env, serv, None),
        },
        TypeInner::Class(ref args, ref t) => match syntax {
            Some(IDLActorType {
                typ: IDLType::ClassT(_, syntax_t),
                docs,
            }) => {
                let docs = pp_docs(docs);
                docs.append(self_doc)
                    .append(pp_class(env, (args, t), Some(syntax_t)))
            }
            _ => self_doc.append(pp_class(env, (args, t), None)),
        },
        TypeInner::Var(_) => self_doc.append(pp_ty(env, ty)),
        _ => unreachable!(),
    }
}

pub fn compile(env: &TypeEnv, actor: &Option<Type>, prog: &IDLMergedProg) -> String {
    let header = r#"// This is a generated Motoko binding.
// Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.
"#;
    let syntax_actor = prog.resolve_actor().ok().flatten();
    let doc = match actor {
        None => pp_defs(env, prog),
        Some(actor) => {
            let defs = pp_defs(env, prog);
            let actor = pp_actor(env, actor, syntax_actor.as_ref());
            defs.append(actor)
        }
    };
    let doc = RcDoc::text(header)
        .append(RcDoc::line())
        .append("module ")
        .append(enclose_space("{", doc, "}"))
        .pretty(LINE_WIDTH)
        .to_string();
    doc
}
