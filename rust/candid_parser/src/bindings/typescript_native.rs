use super::javascript::is_tuple;
use candid::pretty::utils::*;
use candid::types::{Field, Function, Label, SharedLabel, Type, TypeEnv, TypeInner};
use pretty::RcDoc;

fn indent4<'a>() -> RcDoc<'a> {
    RcDoc::space()
        .append(RcDoc::space())
        .append(RcDoc::space())
        .append(RcDoc::space())
}

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
        // Primitive types remain unchanged
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
        Opt(ref t) => {
            // For nested options, use Option<T> helper
            // For simple options, use T | null
            match t.as_ref() {
                TypeInner::Opt(_) => str("Option<")
                    .append(pp_ty(env, t, is_ref))
                    .append(str(">")),
                _ => pp_ty(env, t, is_ref).append(str(" | null")),
            }
        }
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
                // Directly create array notation without enclose which adds newlines
                _ => str("Array<").append(pp_ty(env, t, is_ref)).append(str(">")),
            }
        }
        Record(ref fs) => {
            if is_tuple(ty) {
                // Use direct intersperse to keep tuples on one line without line breaks
                let tuple_items = fs.iter().map(|f| pp_ty(env, &f.ty, is_ref));
                str("[")
                    .append(RcDoc::intersperse(tuple_items, str(", ")))
                    .append(str("]"))
            } else {
                // Use direct intersperse for record fields too
                let fields = fs.iter().map(|f| pp_field(env, f, is_ref));
                str("{ ")
                    .append(RcDoc::intersperse(fields, str(", ")))
                    .append(str(" }"))
            }
        }
        Variant(ref fs) => {
            if fs.is_empty() {
                str("never")
            } else {
                // Replace strict_concat with direct intersperse for variants
                let variants = fs
                    .iter()
                    .map(|f| str("{ ").append(pp_field(env, f, is_ref)).append(str(" }")));
                RcDoc::intersperse(variants, str(" | "))
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

    // Use direct intersperse for arguments to keep them on one line
    let args = RcDoc::intersperse(args_docs, str(", "));

    let rets = match func.rets.len() {
        0 => str("void"),
        1 => pp_ty(env, &func.rets[0], true),
        _ => {
            // Use direct intersperse for multiple return types
            let ret_types = func.rets.iter().map(|ty| pp_ty(env, ty, true));
            str("[")
                .append(RcDoc::intersperse(ret_types, str(", ")))
                .append(str("]"))
        }
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

fn pp_service_interface<'a>(
    env: &'a TypeEnv,
    id: &'a str,
    serv: &'a [(String, Type)],
) -> RcDoc<'a> {
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

    kwd("export interface")
        .append(ident(id))
        .append(" ")
        .append(RcDoc::text("{"))
        .append(RcDoc::line())
        .append(doc_with_commas)
        .append(RcDoc::line())
        .append(RcDoc::text("}"))
}

fn pp_actor_var_wrapper<'a>(env: &'a TypeEnv, service_name: &'a str, id: &'a str) -> RcDoc<'a> {
    let type_ref = env.find_type(id).unwrap();
    // Determine the inner service details, which could be directly a service
    // or could be a variable reference to a service
    let serv = match type_ref.as_ref() {
        TypeInner::Service(ref serv) => serv,
        TypeInner::Var(var_id) => {
            // If it's a variable, find what it refers to
            let referred_type = env.rec_find_type(var_id).unwrap();
            match referred_type.as_ref() {
                TypeInner::Service(ref serv) => serv,
                _ => unreachable!("Expected service type for {}", var_id),
            }
        }
        _ => unreachable!("Expected service or reference to service type"),
    };

    kwd("export interface ")
        .append(ident(service_name))
        .append(" extends ")
        .append(ident(id))
        .append(" {}")
        .append(RcDoc::line())
        .append(RcDoc::line())
        .append("export class ")
        .append(ident(service_name))
        .append(" implements ")
        .append(ident(service_name))
        .append(pp_wrapper(env, service_name, serv))
}

fn pp_actor_service_wrapper<'a>(
    env: &'a TypeEnv,
    service_name: &'a str,
    serv: &'a Vec<(String, Type)>,
) -> RcDoc<'a> {
    pp_service_interface(env, service_name, serv)
        .append(RcDoc::line())
        .append(RcDoc::line())
        .append("export class ")
        .append(ident(service_name))
        .append(" ")
        .append(RcDoc::text("implements"))
        .append(ident(service_name))
        .append(pp_wrapper(env, service_name, serv))
}

fn pp_wrapper<'a>(
    env: &'a TypeEnv,
    service_name: &'a str,
    serv: &'a Vec<(String, Type)>,
) -> RcDoc<'a> {
    let doc = serv.iter().map(|(method_id, func)| {
        let func_doc = match func.as_ref() {
            TypeInner::Func(ref func) => {
                // Use ident instead of quote_ident to avoid quotes
                ident(method_id)
                    .append(pp_function(env, func))
                    .append(" {")
                    .append(RcDoc::line())
                    // Use the generate_function_wrapper function to create the wrapper body
                    .append(indent4())
                    .append(indent4())
                    .append(generate_function_wrapper(env, func, method_id))
                    .append(RcDoc::line())
                    .append(indent4())
                    .append(str("}"))
            }
            _ => ident(method_id)
                .append(kwd(":"))
                .append(pp_ty(env, func, false)),
        };
        // Add 4 spaces indentation at the beginning of each line (class level)
        RcDoc::nil().append(indent4()).append(func_doc)
    });

    let doc_with_lines = RcDoc::intersperse(doc, RcDoc::line());

    kwd(" {") // Only one set of braces
        .append(RcDoc::line())
        .append(indent4())
        .append("private _actor: ActorSubclass<_SERVICE>;")
        .append(RcDoc::line())
        .append(indent4())
        .append(RcDoc::text("constructor() {"))
        .append(RcDoc::line())
        .append(indent4())
        .append(indent4())
        .append(RcDoc::text(format!("this._actor = _{};", service_name)))
        .append(RcDoc::line())
        .append(indent4())
        .append(RcDoc::text("}"))
        .append(RcDoc::line())
        .append(doc_with_lines)
        .append(RcDoc::line())
        .append(RcDoc::line())
        .append(RcDoc::space())
        .append(RcDoc::line())
        .append(str("}")) // Closing brace
}

// Function to generate definitions for types
fn pp_defs<'a>(env: &'a TypeEnv, def_list: &'a [&'a str]) -> RcDoc<'a> {
    lines(def_list.iter().map(|id| {
        if let Ok(ty) = env.find_type(id) {
            let export = match ty.as_ref() {
                TypeInner::Record(_) if !is_tuple(ty) => kwd("export interface")
                    .append(ident(id))
                    .append(" ")
                    .append(pp_ty(env, ty, false)),
                TypeInner::Service(ref serv) => pp_service_interface(env, id, serv),
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
        } else {
            // Handle case where type is not found
            kwd("// Type not found: ").append(str(id))
        }
    }))
}

fn convert<'a>(env: &'a TypeEnv, i: usize, ty: &'a Type, arg: &'a str) -> RcDoc<'a> {
    RcDoc::nil()
}

// Generate function wrapper with conversions
pub fn generate_function_wrapper<'a>(
    env: &'a TypeEnv,
    func: &'a Function,
    method_name: &'a str,
) -> RcDoc<'a> {
    // Generate parameter conversions (TypeScript -> Candid)
    let param_conversions = func
        .args
        .iter()
        .enumerate()
        .map(|(i, ty)| convert(env, i, ty, ""));

    // Join parameter conversions with newlines
    let param_conversions_doc = RcDoc::intersperse(param_conversions, RcDoc::line());

    // Generate the function call with converted arguments
    let arg_names = (0..func.args.len()).map(|i| str("_arg").append(RcDoc::as_string(i)));
    let args_list = RcDoc::intersperse(arg_names, str(", "));

    // Generate result conversion (Candid -> TypeScript)
    let return_conversion = match func.rets.len() {
        0 => str("return;"),
        1 => {
            let conversion = convert(env, 0, &func.rets[0], "");
            str("const _result0 = await this._actor.")
                .append(str(method_name))
                .append(str("("))
                .append(args_list)
                .append(str(");"))
                .append(RcDoc::line())
                .append(conversion)
                .append(RcDoc::line())
                .append(str("return result0;"))
        }
        _ => {
            // Handle multi-value returns
            let result_decl = str("const [")
                .append(RcDoc::intersperse(
                    (0..func.rets.len()).map(|i| str("_result").append(RcDoc::as_string(i))),
                    str(", "),
                ))
                .append(str("] = await this._actor."))
                .append(str(method_name))
                .append(str("("))
                .append(args_list.clone())
                .append(str(");"));

            let result_conversions = func
                .rets
                .iter()
                .enumerate()
                .map(|(i, ty)| convert(env, i, ty, ""));

            let return_statement = str("return [")
                .append(RcDoc::intersperse(
                    (0..func.rets.len()).map(|i| str("result").append(RcDoc::as_string(i))),
                    str(", "),
                ))
                .append(str("];"));

            result_decl
                .append(RcDoc::line())
                .append(RcDoc::intersperse(result_conversions, RcDoc::line()))
                .append(RcDoc::line())
                .append(return_statement)
        }
    };

    // Combine all parts into the function wrapper
    param_conversions_doc
        .append(RcDoc::line())
        .append(return_conversion)
}

fn pp_actor<'a>(env: &'a TypeEnv, ty: &'a Type, service_name: &'a str) -> RcDoc<'a> {
    match ty.as_ref() {
        TypeInner::Service(ref serv) => pp_actor_service_wrapper(env, service_name, serv),
        TypeInner::Var(id) => pp_actor_var_wrapper(env, service_name, id),
        TypeInner::Class(_, t) => pp_actor(env, t, service_name),
        _ => unreachable!(),
    }
}

fn helper_optional_ts_type<'a>(_env: &'a TypeEnv) -> RcDoc<'a> {
    RcDoc::text("type Some<T> = {")
        .append(RcDoc::line())
        .append(RcDoc::text("    _tag: \"Some\","))
        .append(RcDoc::line())
        .append(RcDoc::text("    value: T"))
        .append(RcDoc::line())
        .append(RcDoc::text("}"))
        .append(RcDoc::line())
        .append(RcDoc::line())
        .append(RcDoc::text("type None = {"))
        .append(RcDoc::line())
        .append(RcDoc::text("    _tag: \"None\""))
        .append(RcDoc::line())
        .append(RcDoc::text("}"))
        .append(RcDoc::line())
        .append(RcDoc::line())
        .append(RcDoc::text("type Option<T> = Some<T> | None"))
}

fn pp_imports_exports<'a>(service_name: &'a str, _original_name: &'a str) -> RcDoc<'a> {
    let imports = format!(
        r#"import {{ {original_name} as _{original_name} }} from './{dashed_name}';
import type {{
  ActorSubclass,
}} from "@dfinity/agent";
import {{ _SERVICE }} from './{dashed_name}/{dashed_name}.did';"#,
        original_name = service_name,
        dashed_name = service_name.replace('-', "_")
    );

    RcDoc::text(imports)
        .append(RcDoc::line().append(RcDoc::line()))
        .append(RcDoc::line().append(RcDoc::line()))
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

    let helpers = helper_optional_ts_type(env);

    let imports_exports_doc = pp_imports_exports(service_name, service_name);

    let doc = RcDoc::text(header)
        .append(RcDoc::line())
        .append(RcDoc::line()) // Add an extra blank line
        .append(imports_exports_doc)
        .append(RcDoc::line())
        .append(RcDoc::line())
        .append(helpers)
        .append(RcDoc::line())
        .append(RcDoc::line())
        .append(defs)
        .append(actor);
    doc.pretty(LINE_WIDTH).to_string()
}
