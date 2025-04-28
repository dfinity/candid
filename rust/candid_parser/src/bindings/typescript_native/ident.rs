use swc_core::common::{SyntaxContext, DUMMY_SP};
use swc_core::ecma::ast::*;

pub static KEYWORDS: [&str; 125] = [
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

pub fn get_ident(name: &str) -> Ident {
    Ident::new(name.into(), DUMMY_SP, SyntaxContext::empty())
}

pub fn get_typescript_ident(name: &str, filter_keywords: bool) -> String {
    // Handle empty names by returning a quoted empty string
    if name.is_empty() {
        return "\"\"".to_string();
    }

    if filter_keywords && KEYWORDS.contains(&name) {
        return format!("{}_", name);
    }

    if name.chars().any(|c| !c.is_ascii_alphanumeric() && c != '_') {
        // If the name contains non-alphanumeric characters (except underscore),
        // or contains quotes, we need to quote it to make it a valid TypeScript property name
        return format!("'{}'", name.escape_debug());
    } else {
        return name.to_string();
    }
}

pub fn contains_unicode_characters(name: &str) -> bool {
    name != get_typescript_ident(name, false)
}

pub fn get_ident_guarded(name: &str) -> Ident {
    let ident_name = get_typescript_ident(name, true);
    get_ident(&ident_name)
}

pub fn get_ident_guarded_keyword_ok(name: &str) -> Ident {
    let ident_name: String = get_typescript_ident(name, false);
    get_ident(&ident_name)
}

pub fn get_ident_field(name: &str) -> Ident {
    let ident_name: String = format!("'{}'", name.escape_debug());
    get_ident(&ident_name)
}
