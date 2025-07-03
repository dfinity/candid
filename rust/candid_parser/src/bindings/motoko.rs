// This module implements the Candid to Motoko binding as specified in
// https://github.com/dfinity/motoko/blob/master/design/IDL-Motoko.md

use candid::pretty::candid::is_valid_as_id;
use candid::pretty::utils::*;
use candid::types::syntax::{self, IDLMergedProg, IDLType};
use candid::types::{ArgType, Field, FuncMode, Function, Label, SharedLabel, Type, TypeInner};
use candid::TypeEnv;
use pretty::RcDoc;

const DOC_COMMENT_PREFIX: &str = "/// ";

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

fn pp_ty<'a>(ty: &'a Type, syntax: Option<&'a IDLType>) -> RcDoc<'a> {
    match (ty.as_ref(), syntax) {
        (TypeInner::Null, _) => str("Null"),
        (TypeInner::Bool, _) => str("Bool"),
        (TypeInner::Nat, _) => str("Nat"),
        (TypeInner::Int, _) => str("Int"),
        (TypeInner::Nat8, _) => str("Nat8"),
        (TypeInner::Nat16, _) => str("Nat16"),
        (TypeInner::Nat32, _) => str("Nat32"),
        (TypeInner::Nat64, _) => str("Nat64"),
        (TypeInner::Int8, _) => str("Int8"),
        (TypeInner::Int16, _) => str("Int16"),
        (TypeInner::Int32, _) => str("Int32"),
        (TypeInner::Int64, _) => str("Int64"),
        (TypeInner::Float32, _) => panic!("float32 not supported in Motoko"),
        (TypeInner::Float64, _) => str("Float"),
        (TypeInner::Text, _) => str("Text"),
        (TypeInner::Reserved, _) => str("Any"),
        (TypeInner::Empty, _) => str("None"),
        (TypeInner::Var(ref s), _) => escape(s, false),
        (TypeInner::Principal, _) => str("Principal"),
        (TypeInner::Opt(ref t), maybe_syntax_opt) => {
            str("?").append(pp_ty(t, maybe_syntax_opt.map(|o| o.opt_inner())))
        }
        (TypeInner::Vec(ref t), maybe_syntax_vec) => {
            if matches!(t.as_ref(), TypeInner::Nat8) {
                str("Blob")
            } else {
                enclose("[", pp_ty(t, maybe_syntax_vec.map(|v| v.vec_inner())), "]")
            }
        }
        (TypeInner::Record(ref fs), maybe_syntax_record) => pp_record(
            fs,
            maybe_syntax_record.map(|s| s.record_fields()),
            is_tuple(ty),
        ),
        (TypeInner::Variant(ref fs), maybe_syntax_variant) => {
            pp_variant(fs, maybe_syntax_variant.map(|v| v.variant_fields()))
        }
        (TypeInner::Func(ref func), _) => pp_function(func),
        (TypeInner::Service(ref meths), maybe_syntax_service) => {
            pp_service(meths, maybe_syntax_service.map(|s| s.service_methods()))
        }
        (TypeInner::Class(ref args, ref t), maybe_syntax_class) => {
            let doc = pp_args(args).append(" -> async ");
            let maybe_syntax_serv = maybe_syntax_class.map(|c| {
                if let IDLType::ClassT(_, s) = c {
                    s.as_ref()
                } else {
                    unreachable!()
                }
            });
            let service_doc = match t.as_ref() {
                TypeInner::Service(_) => pp_ty(t, maybe_syntax_serv.map(|s| s.as_service())),
                TypeInner::Var(_) => pp_ty(t, maybe_syntax_serv.map(|v| v.as_var())),
                _ => unreachable!(),
            };
            doc.append(service_doc)
        }
        (TypeInner::Knot(_), _) | (TypeInner::Unknown, _) | (TypeInner::Future, _) => {
            unreachable!()
        }
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

fn pp_field<'a>(field: &'a Field, syntax: Option<&'a syntax::TypeField>) -> RcDoc<'a> {
    pp_label(&field.id)
        .append(" : ")
        .append(pp_ty(&field.ty, syntax.map(|s| &s.typ)))
}

fn pp_record<'a>(
    fields: &'a [Field],
    syntax: Option<&'a [syntax::TypeField]>,
    is_tuple: bool,
) -> RcDoc<'a> {
    if is_tuple {
        let tuple = concat(fields.iter().map(|f| pp_ty(&f.ty, None)), ",");
        enclose("(", tuple, ")")
    } else {
        let fields = concat(
            fields.iter().map(|f| {
                let syntax_field =
                    syntax.and_then(|tfs| tfs.iter().find(|tf| &tf.label == f.id.as_ref()));
                pp_docs(syntax_field.map(|tf| tf.docs.as_slice())).append(pp_field(f, syntax_field))
            }),
            ";",
        );
        enclose_space("{", fields, "}")
    }
}

fn pp_variant<'a>(fields: &'a [Field], syntax: Option<&'a [syntax::TypeField]>) -> RcDoc<'a> {
    if fields.is_empty() {
        str("{#}")
    } else {
        let fields = concat(
            fields.iter().map(|f| {
                let syntax_field =
                    syntax.and_then(|tfs| tfs.iter().find(|tf| &tf.label == f.id.as_ref()));
                pp_docs(syntax_field.map(|tf| tf.docs.as_slice()))
                    .append(pp_variant_field(f, syntax_field))
            }),
            ";",
        );
        enclose_space("{", fields, "}")
    }
}

fn pp_variant_field<'a>(field: &'a Field, syntax: Option<&'a syntax::TypeField>) -> RcDoc<'a> {
    let doc = str("#").append(pp_label(&field.id));
    if *field.ty != TypeInner::Null {
        doc.append(" : ")
            .append(pp_ty(&field.ty, syntax.map(|s| &s.typ)))
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
                enclose("(", pp_ty(&ty.typ, None), ")")
            } else {
                pp_ty(&ty.typ, None)
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
                    escape(name, false)
                        .append(" : ")
                        .append(pp_ty(&arg.typ, None))
                } else {
                    pp_ty(&arg.typ, None)
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
                enclose("(", pp_ty(ty, None), ")")
            } else {
                pp_ty(ty, None)
            }
        }
        _ => {
            let doc = concat(args.iter().map(|arg| pp_ty(arg, None)), ",");
            enclose("(", doc, ")")
        }
    }
}

fn pp_service<'a>(serv: &'a [(String, Type)], syntax: Option<&'a [syntax::Binding]>) -> RcDoc<'a> {
    let doc = concat(
        serv.iter().map(|(id, func)| {
            pp_docs(
                syntax
                    .and_then(|bs| bs.iter().find(|b| &b.id == id))
                    .map(|b| b.docs.as_slice()),
            )
            .append(escape(id, true))
            .append(" : ")
            .append(pp_ty(func, None))
        }),
        ";",
    );
    kwd("actor").append(enclose_space("{", doc, "}"))
}

fn pp_docs<'a>(docs: Option<&'a [String]>) -> RcDoc<'a> {
    docs.map(|docs| {
        lines(
            docs.iter()
                .map(|line| RcDoc::text(DOC_COMMENT_PREFIX).append(line)),
        )
    })
    .unwrap_or(RcDoc::nil())
}

fn pp_defs<'a>(env: &'a TypeEnv, prog: &'a IDLMergedProg) -> RcDoc<'a> {
    lines(env.0.iter().map(|(id, ty)| {
        let syntax = prog.lookup(id);
        let docs = pp_docs(syntax.map(|b| b.docs.as_slice()));
        docs.append(kwd("public type"))
            .append(escape(id, false))
            .append(" = ")
            .append(pp_ty(ty, syntax.map(|b| &b.typ)))
            .append(";")
    }))
}

fn pp_actor<'a>(ty: &'a Type, syntax: Option<&'a IDLType>) -> RcDoc<'a> {
    match ty.as_ref() {
        TypeInner::Service(_) | TypeInner::Var(_) | TypeInner::Class(_, _) => pp_ty(ty, syntax),
        _ => unreachable!(),
    }
}

pub fn compile(env: &TypeEnv, actor: &Option<Type>, prog: &IDLMergedProg) -> String {
    let header = r#"// This is a generated Motoko binding.
// Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.
"#;
    let doc = match actor {
        None => pp_defs(env, prog),
        Some(actor) => {
            let syntax = prog.actor();
            let defs = pp_defs(env, prog);
            let actor = kwd("public type Self =").append(pp_actor(actor, syntax.map(|a| &a.typ)));
            defs.append(pp_docs(syntax.map(|a| a.docs.as_slice())).append(actor))
        }
    };
    RcDoc::text(header)
        .append(RcDoc::line())
        .append("module ")
        .append(enclose_space("{", doc, "}"))
        .pretty(LINE_WIDTH)
        .to_string()
}
