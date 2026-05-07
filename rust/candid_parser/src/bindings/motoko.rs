// This module implements the Candid to Motoko binding as specified in
// https://github.com/dfinity/motoko/blob/master/design/IDL-Motoko.md

use crate::syntax::{self, IDLActorType, IDLMergedProg, IDLType};
use candid::pretty::candid::is_valid_as_id;
use candid::pretty::utils::*;
use candid::types::{Field, FuncMode, Function, Label, SharedLabel, Type, TypeInner};
use candid::TypeEnv;
use pretty::RcDoc;
use std::collections::HashMap;

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

// Capitalises the first letter and each letter following '_', stripping
// underscores. Returns None for names that don't start with a lowercase letter;
// those are left as-is by build_names. A trailing '_' is silently consumed
// (the capitalize flag is set but no character follows).
fn to_pascal_case(s: &str) -> Option<String> {
    if !s.starts_with(|c: char| c.is_ascii_lowercase()) {
        return None;
    }
    let mut out = String::with_capacity(s.len());
    let mut capitalize = true;
    for c in s.chars() {
        if c == '_' {
            capitalize = true;
        } else if capitalize {
            out.extend(c.to_uppercase());
            capitalize = false;
        } else {
            out.push(c);
        }
    }
    Some(out)
}

// Precomputes the display name for every type alias in env. Used once at the
// top of compile so all printer functions can do O(1) name lookups.
//
// A PascalCase name is used when it is unambiguous: no other name in env maps
// to the same PascalCase form (count == 1), the result is not the reserved
// "Self", and no verbatim env key already has that name.
fn build_names(env: &TypeEnv) -> HashMap<String, String> {
    let mut pascal_counts: HashMap<String, usize> = HashMap::new();
    for id in env.0.keys() {
        if let Some(pascal) = to_pascal_case(id) {
            *pascal_counts.entry(pascal).or_default() += 1;
        }
    }

    env.0
        .keys()
        .map(|id| {
            let display = match to_pascal_case(id) {
                Some(pascal)
                    if pascal_counts.get(&pascal).copied() == Some(1)
                        && pascal != "Self"
                        && !env.0.contains_key(&pascal) =>
                {
                    pascal
                }
                _ => {
                    let fallback = escape_str(id);
                    // escape_str doesn't reserve "Self"; guard explicitly.
                    if fallback == "Self" {
                        format!("{fallback}_")
                    } else {
                        fallback
                    }
                }
            };
            (id.clone(), display)
        })
        .collect()
}

#[derive(Copy, Clone)]
struct BindingCtx<'a> {
    env: &'a TypeEnv,
    names: &'a HashMap<String, String>,
}

fn pp_ty_rich<'a>(ctx: BindingCtx<'a>, ty: &'a Type, syntax: Option<&'a IDLType>) -> RcDoc<'a> {
    match (ty.as_ref(), syntax) {
        (TypeInner::Service(ref meths), Some(IDLType::ServT(methods))) => {
            pp_service(ctx, meths, Some(methods))
        }
        (TypeInner::Class(ref args, t), Some(IDLType::ClassT(_, syntax_t))) => {
            pp_class(ctx, (args, t), Some(syntax_t))
        }
        (TypeInner::Record(ref fields), Some(IDLType::RecordT(syntax_fields))) => {
            pp_record(ctx, fields, Some(syntax_fields))
        }
        (TypeInner::Variant(ref fields), Some(IDLType::VariantT(syntax_fields))) => {
            pp_variant(ctx, fields, Some(syntax_fields))
        }
        (TypeInner::Opt(ref inner), Some(IDLType::OptT(syntax))) => {
            str("?").append(pp_ty_rich(ctx, inner, Some(syntax)))
        }
        (TypeInner::Vec(ref inner), Some(IDLType::VecT(syntax))) => {
            pp_vec(ctx, inner, Some(syntax))
        }
        (_, _) => pp_ty(ctx, ty),
    }
}

fn pp_ty<'a>(ctx: BindingCtx<'a>, ty: &'a Type) -> RcDoc<'a> {
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
        Var(ref s) => RcDoc::text(ctx.names.get(s).cloned().unwrap_or_else(|| escape_str(s))),
        Principal => str("Principal"),
        Opt(ref t) => str("?").append(pp_ty(ctx, t)),
        Vec(ref t) => pp_vec(ctx, t, None),
        Record(ref fs) => pp_record(ctx, fs, None),
        Variant(ref fs) => pp_variant(ctx, fs, None),
        Func(ref func) => pp_function(ctx, func),
        Service(ref serv) => pp_service(ctx, serv, None),
        Class(ref args, ref t) => pp_class(ctx, (args, t), None),
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

fn pp_function<'a>(ctx: BindingCtx<'a>, func: &'a Function) -> RcDoc<'a> {
    let args = pp_args(ctx, &func.args);
    let rets = pp_rets(ctx, &func.rets);
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

fn pp_args<'a>(ctx: BindingCtx<'a>, args: &'a [Type]) -> RcDoc<'a> {
    match args {
        [ty] => {
            if is_tuple(ty) {
                enclose("(", pp_ty(ctx, ty), ")")
            } else {
                pp_ty(ctx, ty)
            }
        }
        _ => {
            let doc = concat(args.iter().map(|ty| pp_ty(ctx, ty)), ",");
            enclose("(", doc, ")")
        }
    }
}

fn pp_rets<'a>(ctx: BindingCtx<'a>, args: &'a [Type]) -> RcDoc<'a> {
    pp_args(ctx, args)
}

fn pp_service<'a>(
    ctx: BindingCtx<'a>,
    serv: &'a [(String, Type)],
    syntax: Option<&'a [syntax::Binding]>,
) -> RcDoc<'a> {
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
            .append(pp_ty_rich(ctx, func, syntax_field_ty))
    });
    kwd("actor").append(enclose_space("{", concat(methods, ";"), "}"))
}

fn pp_tuple<'a>(ctx: BindingCtx<'a>, fields: &'a [Field]) -> RcDoc<'a> {
    let tuple = concat(fields.iter().map(|f| pp_ty(ctx, &f.ty)), ",");
    enclose("(", tuple, ")")
}

fn pp_vec<'a>(ctx: BindingCtx<'a>, inner: &'a Type, syntax: Option<&'a IDLType>) -> RcDoc<'a> {
    if matches!(inner.as_ref(), TypeInner::Nat8) {
        str("Blob")
    } else {
        enclose("[", pp_ty_rich(ctx, inner, syntax), "]")
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

fn pp_record<'a>(
    ctx: BindingCtx<'a>,
    fields: &'a [Field],
    syntax: Option<&'a [syntax::TypeField]>,
) -> RcDoc<'a> {
    if is_tuple_fields(fields) {
        return pp_tuple(ctx, fields);
    }
    let fields = fields.iter().map(|field| {
        let (docs, syntax_field) = find_field(syntax, &field.id);
        docs.append(pp_label(&field.id))
            .append(" : ")
            .append(pp_ty_rich(ctx, &field.ty, syntax_field))
    });
    enclose_space("{", concat(fields, ";"), "}")
}

fn pp_variant<'a>(
    ctx: BindingCtx<'a>,
    fields: &'a [Field],
    syntax: Option<&'a [syntax::TypeField]>,
) -> RcDoc<'a> {
    if fields.is_empty() {
        return str("{#}");
    }
    let fields = fields.iter().map(|field| {
        let (docs, syntax_field) = find_field(syntax, &field.id);
        let doc = docs.append(str("#")).append(pp_label(&field.id));
        if *field.ty != TypeInner::Null {
            doc.append(" : ")
                .append(pp_ty_rich(ctx, &field.ty, syntax_field))
        } else {
            doc
        }
    });
    enclose_space("{", concat(fields, ";"), "}")
}

fn pp_class<'a>(
    ctx: BindingCtx<'a>,
    (args, ty): (&'a [Type], &'a Type),
    syntax: Option<&'a IDLType>,
) -> RcDoc<'a> {
    let doc = pp_args(ctx, args).append(" -> async ");
    match ty.as_ref() {
        TypeInner::Service(_) => doc.append(pp_ty_rich(ctx, ty, syntax)),
        TypeInner::Var(_) => doc.append(pp_ty(ctx, ty)),
        _ => unreachable!(),
    }
}

fn pp_docs<'a>(docs: &'a [String]) -> RcDoc<'a> {
    lines(docs.iter().map(|line| RcDoc::text("/// ").append(line)))
}

fn pp_defs<'a>(ctx: BindingCtx<'a>, prog: &'a IDLMergedProg) -> RcDoc<'a> {
    lines(ctx.env.0.iter().map(|(id, ty)| {
        let syntax = prog.lookup(id);
        let docs = syntax
            .map(|b| pp_docs(b.docs.as_ref()))
            .unwrap_or(RcDoc::nil());
        let name = ctx.names[id].clone();
        docs.append(kwd("public type"))
            .append(RcDoc::text(name))
            .append(" = ")
            .append(pp_ty_rich(ctx, ty, syntax.map(|b| &b.typ)))
            .append(";")
    }))
}

fn pp_actor<'a>(ctx: BindingCtx<'a>, ty: &'a Type, syntax: Option<&'a IDLActorType>) -> RcDoc<'a> {
    let self_doc = kwd("public type Self =");
    match ty.as_ref() {
        TypeInner::Service(ref serv) => match syntax {
            Some(IDLActorType {
                typ: IDLType::ServT(ref fields),
                docs,
            }) => {
                let docs = pp_docs(docs);
                docs.append(self_doc)
                    .append(pp_service(ctx, serv, Some(fields)))
            }
            _ => pp_service(ctx, serv, None),
        },
        TypeInner::Class(ref args, ref t) => match syntax {
            Some(IDLActorType {
                typ: IDLType::ClassT(_, syntax_t),
                docs,
            }) => {
                let docs = pp_docs(docs);
                docs.append(self_doc)
                    .append(pp_class(ctx, (args, t), Some(syntax_t)))
            }
            _ => self_doc.append(pp_class(ctx, (args, t), None)),
        },
        TypeInner::Var(_) => self_doc.append(pp_ty(ctx, ty)),
        _ => unreachable!(),
    }
}

// Separate from `compile` so that `names` and `syntax_actor` (locals in
// `compile`) are provably live for the entire lifetime of the RcDoc they feed.
fn compile_inner<'a>(
    ctx: BindingCtx<'a>,
    actor: &'a Option<Type>,
    syntax_actor: Option<&'a IDLActorType>,
    prog: &'a IDLMergedProg,
) -> String {
    let header = r#"// This is a generated Motoko binding.
// Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.
"#;
    let doc = match actor {
        None => pp_defs(ctx, prog),
        Some(actor) => pp_defs(ctx, prog).append(pp_actor(ctx, actor, syntax_actor)),
    };
    RcDoc::text(header)
        .append(RcDoc::line())
        .append("module ")
        .append(enclose_space("{", doc, "}"))
        .pretty(LINE_WIDTH)
        .to_string()
}

pub fn compile(env: &TypeEnv, actor: &Option<Type>, prog: &IDLMergedProg) -> String {
    let syntax_actor = prog.resolve_actor().ok().flatten();
    let names = build_names(env);
    compile_inner(
        BindingCtx { env, names: &names },
        actor,
        syntax_actor.as_ref(),
        prog,
    )
}
