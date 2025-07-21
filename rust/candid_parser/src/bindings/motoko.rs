// This module implements the Candid to Motoko binding as specified in
// https://github.com/dfinity/motoko/blob/master/design/IDL-Motoko.md

use crate::syntax::{self, IDLActorType, IDLMergedProg, IDLType};
use candid::pretty::candid::is_valid_as_id;
use candid::pretty::utils::*;
use candid::types::{ArgType, Field, FuncMode, Function, Label, SharedLabel, Type, TypeInner};
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

fn pp_ty_rich<'a>(ty: &'a Type, syntax: Option<&'a IDLType>) -> RcDoc<'a> {
    match (ty.as_ref(), syntax) {
        (TypeInner::Service(ref meths), Some(IDLType::ServT(methods))) => {
            pp_service(meths, Some(methods))
        }
        (TypeInner::Class(ref args, t), Some(IDLType::ClassT(_, syntax_t))) => {
            pp_class((args, t), Some(syntax_t))
        }
        (TypeInner::Record(ref fields), Some(IDLType::RecordT(syntax_fields))) => {
            pp_record(fields, Some(syntax_fields))
        }
        (TypeInner::Variant(ref fields), Some(IDLType::VariantT(syntax_fields))) => {
            pp_variant(fields, Some(syntax_fields))
        }
        (TypeInner::Opt(ref inner), Some(IDLType::OptT(syntax))) => {
            str("?").append(pp_ty_rich(inner, Some(syntax)))
        }
        (TypeInner::Vec(ref inner), Some(IDLType::VecT(syntax))) => pp_vec(inner, Some(syntax)),
        (_, _) => pp_ty(ty),
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
        Vec(ref t) => pp_vec(t, None),
        Record(ref fs) => pp_record(fs, None),
        Variant(ref fs) => pp_variant(fs, None),
        Func(ref func) => pp_function(func),
        Service(ref serv) => pp_service(serv, None),
        Class(ref args, ref t) => pp_class((args, t), None),
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
            enclose("(", concat(args, ","), ")")
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
        _ => enclose("(", concat(args.iter().map(pp_ty), ","), ")"),
    }
}

fn pp_service<'a>(serv: &'a [(String, Type)], syntax: Option<&'a [syntax::Binding]>) -> RcDoc<'a> {
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
            .append(pp_ty_rich(func, syntax_field_ty))
    });
    kwd("actor").append(enclose_space("{", concat(methods, ";"), "}"))
}

fn pp_tuple<'a>(fields: &'a [Field]) -> RcDoc<'a> {
    let tuple = concat(fields.iter().map(|f| pp_ty(&f.ty)), ",");
    enclose("(", tuple, ")")
}

fn pp_vec<'a>(inner: &'a Type, syntax: Option<&'a IDLType>) -> RcDoc<'a> {
    if matches!(inner.as_ref(), TypeInner::Nat8) {
        str("Blob")
    } else {
        enclose("[", pp_ty_rich(inner, syntax), "]")
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

fn pp_record<'a>(fields: &'a [Field], syntax: Option<&'a [syntax::TypeField]>) -> RcDoc<'a> {
    if is_tuple_fields(fields) {
        return pp_tuple(fields);
    }
    let fields = fields.iter().map(|field| {
        let (docs, syntax_field) = find_field(syntax, &field.id);
        docs.append(pp_label(&field.id))
            .append(" : ")
            .append(pp_ty_rich(&field.ty, syntax_field))
    });
    enclose_space("{", concat(fields, ";"), "}")
}

fn pp_variant<'a>(fields: &'a [Field], syntax: Option<&'a [syntax::TypeField]>) -> RcDoc<'a> {
    if fields.is_empty() {
        return str("{#}");
    }
    let fields = fields.iter().map(|field| {
        let (docs, syntax_field) = find_field(syntax, &field.id);
        let doc = docs.append(str("#")).append(pp_label(&field.id));
        if *field.ty != TypeInner::Null {
            doc.append(" : ")
                .append(pp_ty_rich(&field.ty, syntax_field))
        } else {
            doc
        }
    });
    enclose_space("{", concat(fields, ";"), "}")
}

fn pp_class<'a>((args, ty): (&'a [ArgType], &'a Type), syntax: Option<&'a IDLType>) -> RcDoc<'a> {
    let doc = pp_args(args).append(" -> async ");
    match ty.as_ref() {
        TypeInner::Service(_) => doc.append(pp_ty_rich(ty, syntax)),
        TypeInner::Var(_) => doc.append(pp_ty(ty)),
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
            .append(escape(id, false))
            .append(" = ")
            .append(pp_ty_rich(ty, syntax.map(|b| &b.typ)))
            .append(";")
    }))
}

fn pp_actor<'a>(ty: &'a Type, syntax: Option<&'a IDLActorType>) -> RcDoc<'a> {
    let self_doc = kwd("public type Self =");
    match ty.as_ref() {
        TypeInner::Service(ref serv) => match syntax {
            Some(IDLActorType {
                typ: IDLType::ServT(ref fields),
                docs,
            }) => {
                let docs = pp_docs(docs);
                docs.append(self_doc).append(pp_service(serv, Some(fields)))
            }
            _ => pp_service(serv, None),
        },
        TypeInner::Class(ref args, ref t) => match syntax {
            Some(IDLActorType {
                typ: IDLType::ClassT(_, syntax_t),
                docs,
            }) => {
                let docs = pp_docs(docs);
                docs.append(self_doc)
                    .append(pp_class((args, t), Some(syntax_t)))
            }
            _ => self_doc.append(pp_class((args, t), None)),
        },
        TypeInner::Var(_) => self_doc.append(pp_ty(ty)),
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
            let actor = pp_actor(actor, syntax_actor.as_ref());
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
