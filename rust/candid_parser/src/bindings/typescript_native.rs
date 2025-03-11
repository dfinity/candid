use super::javascript::is_tuple;
use candid::pretty::utils::*;
use candid::types::{Field, Function, Label, SharedLabel, Type, TypeEnv, TypeInner};
use pretty::RcDoc;

static KEYWORDS: [&str; 125] = [
    // Original JavaScript keywords
    "abstract",
    "arguments",
    "await",
    "boolean",
    "break",
    "byte",
    "case",
    "catch",
    "char",
    "class",
    "const",
    "continue",
    "debugger",
    "default",
    "delete",
    "do",
    "double",
    "else",
    "enum",
    "eval",
    "export",
    "extends",
    "false",
    "final",
    "finally",
    "float",
    "for",
    "function",
    "goto",
    "if",
    "implements",
    "import",
    "in",
    "instanceof",
    "int",
    "interface",
    "let",
    "long",
    "native",
    "new",
    "null",
    "package",
    "private",
    "protected",
    "public",
    "return",
    "short",
    "static",
    "super",
    "switch",
    "synchronized",
    "this",
    "throw",
    "throws",
    "transient",
    "true",
    "try",
    "typeof",
    "var",
    "void",
    "volatile",
    "while",
    "with",
    "yield",
    // TypeScript primitive types
    "any",
    "unknown",
    "never",
    "undefined",
    "object",
    "symbol",
    "bigint",
    "number",
    "string",
    // Utility types
    "Partial",
    "Required",
    "Readonly",
    "Record",
    "Pick",
    "Omit",
    "Exclude",
    "Extract",
    "NonNullable",
    "Parameters",
    "ConstructorParameters",
    "ReturnType",
    "InstanceType",
    "ThisParameterType",
    "OmitThisParameter",
    "ThisType",
    "Uppercase",
    "Lowercase",
    "Capitalize",
    "Uncapitalize",
    // Common built-in types/interfaces
    "Array",
    "ReadonlyArray",
    "Function",
    "Date",
    "Error",
    "Promise",
    "Map",
    "Set",
    "WeakMap",
    "WeakSet",
    "Iterator",
    "IterableIterator",
    "Generator",
    "RegExp",
    "ArrayBuffer",
    "DataView",
    "Float32Array",
    "Float64Array",
    "Int8Array",
    "Int16Array",
    "Int32Array",
    "Uint8Array",
    "Uint16Array",
    "Uint32Array",
    "Uint8ClampedArray",
    "BigInt64Array",
    "BigUint64Array",
    // Common global objects
    "Math",
    "JSON",
    "console",
    "document",
    "window",
];

pub(crate) fn ident(id: &str) -> RcDoc {
    if KEYWORDS.contains(&id) {
        str(id).append("_")
    } else {
        str(id)
    }
}

fn pp_ty<'a>(env: &'a TypeEnv, ty: &'a Type, is_ref: bool) -> RcDoc<'a> {
    use TypeInner::*;
    match ty.as_ref() {
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
        Var(ref id) => {
            if is_ref {
                let ty = env.rec_find_type(id).unwrap();
                if matches!(ty.as_ref(), Service(_) | Func(_)) {
                    pp_ty(env, ty, false)
                } else {
                    ident(id)
                }
            } else {
                ident(id)
            }
        }
        Principal => str("Principal"),
        Opt(ref t) => pp_ty(env, t, is_ref).append(str(" | null")),
        Vec(ref t) => {
            let ty = match t.as_ref() {
                Var(ref id) => {
                    let ty = env.rec_find_type(id).unwrap();
                    if matches!(
                        ty.as_ref(),
                        Nat8 | Nat16 | Nat32 | Nat64 | Int8 | Int16 | Int32 | Int64
                    ) {
                        ty
                    } else {
                        t
                    }
                }
                _ => t,
            };
            match ty.as_ref() {
                Nat8 => str("Uint8Array | number[]"),
                Nat16 => str("Uint16Array | number[]"),
                Nat32 => str("Uint32Array | number[]"),
                Nat64 => str("BigUint64Array | bigint[]"),
                Int8 => str("Int8Array | number[]"),
                Int16 => str("Int16Array | number[]"),
                Int32 => str("Int32Array | number[]"),
                Int64 => str("BigInt64Array | bigint[]"),
                _ => str("Array").append(enclose("<", pp_ty(env, t, is_ref), ">")),
            }
        }
        Record(ref fs) => {
            if is_tuple(ty) {
                let tuple = concat(fs.iter().map(|f| pp_ty(env, &f.ty, is_ref)), ",");
                enclose("[", tuple, "]")
            } else {
                let fields = concat(fs.iter().map(|f| pp_field(env, f, is_ref)), ",");
                enclose_space("{", fields, "}")
            }
        }
        Variant(ref fs) => {
            if fs.is_empty() {
                str("never")
            } else {
                strict_concat(
                    fs.iter()
                        .map(|f| enclose_space("{", pp_field(env, f, is_ref), "}")),
                    " |",
                )
                .nest(INDENT_SPACE)
            }
        }
        Func(ref func) => {
            // Represent functions as regular TypeScript function types
            pp_function_type(env, func)
        }
        Service(_) => str("Principal"),
        Class(_, _) => unreachable!(),
        Knot(_) | Unknown | Future => unreachable!(),
    }
}

fn pp_function_type<'a>(env: &'a TypeEnv, func: &'a Function) -> RcDoc<'a> {
    let args_docs = func.args.iter().enumerate().map(|(i, ty)| {
        str("arg")
            .append(RcDoc::as_string(i))
            .append(str(": "))
            .append(pp_ty(env, ty, true))
    });

    // Use a flat_alt approach to keep args inline
    let args = RcDoc::concat(args_docs.clone().map(|d| d.append(", ")))
        .flat_alt(strict_concat(args_docs, ", "));

    let rets = match func.rets.len() {
        0 => str("void"),
        1 => pp_ty(env, &func.rets[0], true),
        _ => enclose(
            "[",
            concat(func.rets.iter().map(|ty| pp_ty(env, ty, true)), ","),
            "]",
        ),
    };

    str("(").append(args).append(str(") => ")).append(rets)
}

fn pp_label(id: &SharedLabel) -> RcDoc {
    match &**id {
        Label::Named(str) => ident(str),
        Label::Id(n) | Label::Unnamed(n) => str("_")
            .append(RcDoc::as_string(n))
            .append("_")
            .append(RcDoc::space()),
    }
}

fn pp_field<'a>(env: &'a TypeEnv, field: &'a Field, is_ref: bool) -> RcDoc<'a> {
    // Check if the field type is optional
    let is_optional = matches!(field.ty.as_ref(), TypeInner::Opt(_));

    let field_name = pp_label(&field.id);

    // If it's an optional field, add a question mark and unwrap the inner type
    if is_optional {
        if let TypeInner::Opt(inner_type) = field.ty.as_ref() {
            return field_name
                .append(str("?"))
                .append(kwd(":"))
                .append(pp_ty(env, inner_type, is_ref));
        }
    }

    // Regular non-optional field
    field_name
        .append(kwd(":"))
        .append(pp_ty(env, &field.ty, is_ref))
}

fn pp_function<'a>(env: &'a TypeEnv, func: &'a Function) -> RcDoc<'a> {
    let args_docs = func.args.iter().enumerate().map(|(i, ty)| {
        str("arg")
            .append(RcDoc::as_string(i))
            .append(str(": "))
            .append(pp_ty(env, ty, true))
    });

    // Handle the last argument specially to avoid trailing comma
    let args = if func.args.is_empty() {
        RcDoc::nil()
    } else {
        let args_vec: Vec<_> = args_docs.collect();
        let mut result = RcDoc::nil();
        for (i, arg) in args_vec.iter().enumerate() {
            result = result.append(arg.clone());
            if i < args_vec.len() - 1 {
                result = result.append(str(", "));
            }
        }
        result
    };

    let rets = match func.rets.len() {
        0 => str("void"),
        1 => pp_ty(env, &func.rets[0], true),
        _ => enclose(
            "[",
            concat(func.rets.iter().map(|ty| pp_ty(env, ty, true)), ","),
            "]",
        ),
    };

    str("(")
        .append(args)
        .append(str("): Promise<"))
        .append(rets)
        .append(str(">"))
}

fn pp_service<'a>(env: &'a TypeEnv, serv: &'a [(String, Type)]) -> RcDoc<'a> {
    let doc = serv.iter().map(|(id, func)| {
        let func_doc = match func.as_ref() {
            TypeInner::Func(ref func) => {
                // Use ident instead of quote_ident to avoid quotes
                ident(id).append(pp_function(env, func))
            }
            _ => ident(id).append(kwd(":")).append(pp_ty(env, func, false)),
        };
        // Add 4 spaces indentation at the beginning of each line
        RcDoc::space()
            .append(RcDoc::space())
            .append(RcDoc::space())
            .append(RcDoc::space())
            .append(func_doc)
    });

    // Join with comma and newline
    let doc_with_commas = RcDoc::intersperse(doc, RcDoc::text(",").append(RcDoc::line()));

    // Format with line breaks before and after braces
    RcDoc::text("{")
        .append(RcDoc::line())
        .append(doc_with_commas)
        .append(RcDoc::line())
        .append(RcDoc::text("}"))
}

fn pp_defs<'a>(env: &'a TypeEnv, def_list: &'a [&'a str]) -> RcDoc<'a> {
    lines(def_list.iter().map(|id| {
        let ty = env.find_type(id).unwrap();
        let export = match ty.as_ref() {
            TypeInner::Record(_) if !ty.is_tuple() => kwd("export interface")
                .append(ident(id))
                .append(" ")
                .append(pp_ty(env, ty, false)),
            TypeInner::Service(ref serv) => kwd("export interface")
                .append(ident(id))
                .append(" ")
                .append(pp_service(env, serv)),
            TypeInner::Func(ref func) => kwd("export type")
                .append(ident(id))
                .append(" = ")
                .append(pp_function_type(env, func))
                .append(";"),
            _ => kwd("export type")
                .append(ident(id))
                .append(" = ")
                .append(pp_ty(env, ty, false))
                .append(";"),
        };
        export
    }))
}

fn pp_actor<'a>(env: &'a TypeEnv, ty: &'a Type, service_name: &'a str) -> RcDoc<'a> {
    match ty.as_ref() {
        TypeInner::Service(ref serv) => kwd("export interface ")
            .append(str(service_name))
            .append(RcDoc::line())
            .append(pp_service(env, serv)),
        TypeInner::Var(id) => kwd("export interface ")
            .append(str(service_name))
            .append(" extends ")
            .append(str(id))
            .append(str(" {}")),
        TypeInner::Class(_, t) => pp_actor(env, t, service_name),
        _ => unreachable!(),
    }
}

pub fn compile(env: &TypeEnv, actor: &Option<Type>, service_name: &str) -> String {
    let header = r#"import type { Principal } from '@dfinity/principal';
"#;
    let def_list: Vec<_> = env.0.iter().map(|pair| pair.0.as_ref()).collect();
    let defs = pp_defs(env, &def_list);
    let actor = match actor {
        None => RcDoc::nil(),
        Some(actor) => pp_actor(env, actor, service_name),
    };
    let doc = RcDoc::text(header)
        .append(RcDoc::line())
        .append(RcDoc::line()) // Add an extra blank line
        .append(defs)
        .append(actor);
    doc.pretty(LINE_WIDTH).to_string()
}
