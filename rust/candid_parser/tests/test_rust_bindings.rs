//! Structural checks on the generated Rust bindings.
//!
//! The goldenfiles in `tests/assets/ok` record what the generator emits, but they cannot state
//! that the output is *safe*: a regression would simply be blessed into the goldenfile. These
//! tests assert the properties instead.

use candid::types::TypeEnv;
use candid_parser::bindings::rust::{compile, Config, ExternalConfig};
use candid_parser::configs::Configs;
use candid_parser::syntax::{IDLMergedProg, IDLProg};
use candid_parser::typing::check_prog;
use std::str::FromStr;

/// Generate Rust bindings for an in-memory Candid program.
fn compile_did(source: &str) -> String {
    let prog: IDLProg = source.parse().unwrap();
    let mut env = TypeEnv::new();
    let actor = check_prog(&mut env, &prog).unwrap();
    let merged = IDLMergedProg::new(prog);

    let config = Config::new(Configs::from_str("").unwrap());
    let mut external = ExternalConfig::default();
    external
        .0
        .insert("canister_id".to_string(), "aaaaa-aa".to_string());
    let (content, _unused) = compile(&config, &env, &actor, &merged, external);
    content
}

/// Describe the top-level items of a Rust source file, as `kind` or `kind:name` labels.
///
/// Deliberately coarse: the point is to compare the *shape* of two generated files, not to pin
/// down the template, so this survives ordinary changes to what the generator emits.
fn item_shape(source: &str) -> Vec<String> {
    let file = syn::parse_file(source)
        .unwrap_or_else(|e| panic!("generated bindings are not valid Rust: {e}\n\n{source}"));
    file.items
        .iter()
        .map(|item| match item {
            syn::Item::Use(_) => "use".to_string(),
            syn::Item::Macro(m) => {
                let path = m
                    .mac
                    .path
                    .segments
                    .iter()
                    .map(|s| s.ident.to_string())
                    .collect::<Vec<_>>()
                    .join("::");
                format!("macro:{path}!")
            }
            syn::Item::Const(c) => format!("const:{}", c.ident),
            syn::Item::Static(s) => format!("static:{}", s.ident),
            syn::Item::Struct(s) => format!("struct:{}", s.ident),
            syn::Item::Enum(e) => format!("enum:{}", e.ident),
            syn::Item::Type(t) => format!("type:{}", t.ident),
            syn::Item::Fn(f) => format!("fn:{}", f.sig.ident),
            syn::Item::Mod(m) => format!("mod:{}", m.ident),
            syn::Item::Impl(_) => "impl".to_string(),
            other => format!("other:{other:?}"),
        })
        .collect()
}

/// A service type whose method names need escaping, and the same service with plain names.
///
/// The method names of a service *type* are emitted as Rust string literals inside
/// `candid::define_service!`. A Candid method name is an arbitrary text value, so it can contain
/// quotes, backslashes, comment markers and newlines. Escaping them is what keeps a name inside
/// its literal instead of being parsed as Rust.
///
/// The first name is the case that matters: unescaped, it closes both the literal and the macro
/// invocation and leaves the remainder as a well-formed item, so the generated bindings still
/// compile and the breakout is silent. The rest cover the other characters that can end a literal.
const NEEDS_ESCAPING: &str = r#"
type f = func () -> ();
type inner = service {
  "quote\" : F::ty() }); const marker: u32 = ({ 0 //" : f;
  "backslash\\" : f;
  "newline\nand carriage return\r" : f;
  "tab\tand semicolon;" : f;
  "comment markers // and /* */" : f;
  "braces { } and parens ( )" : f;
};
service : { use_inner : (inner) -> (); };
"#;

const PLAIN: &str = r#"
type f = func () -> ();
type inner = service {
  "m0" : f;
  "m1" : f;
  "m2" : f;
  "m3" : f;
  "m4" : f;
  "m5" : f;
};
service : { use_inner : (inner) -> (); };
"#;

#[test]
fn service_method_names_do_not_change_the_generated_item_structure() {
    // Method names of a service type reach the output only as string literal *contents*, so names
    // needing escapes must produce exactly the same items as plain ones. Any difference means a
    // name left its literal and was parsed as Rust.
    assert_eq!(
        item_shape(&compile_did(NEEDS_ESCAPING)),
        item_shape(&compile_did(PLAIN))
    );
}

#[test]
fn service_method_names_are_escaped_not_dropped() {
    let content = compile_did(NEEDS_ESCAPING);
    // The names survive verbatim, in escaped form: `define_service!` receives the original Candid
    // method name as the *value* of a well-formed Rust string literal.
    for expected in [
        r#""quote\" : F::ty() }); const marker: u32 = ({ 0 //""#,
        r#""backslash\\""#,
        r#""newline\nand carriage return\r""#,
        r#""tab\tand semicolon;""#,
        r#""comment markers // and /* */""#,
        r#""braces { } and parens ( )""#,
    ] {
        assert!(
            content.contains(expected),
            "expected escaped method name {expected} in:\n{content}"
        );
    }
}
