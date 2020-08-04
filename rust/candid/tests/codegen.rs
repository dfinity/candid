#![cfg(test)]
use candid::codegen::rust::idl_to_rust;
use candid::IDLProg;
use pretty_assertions::assert_eq;
use std::path::Path;
use std::str::FromStr;

fn run_formatter(rust: String) -> String {
    let mut config = rustfmt::config::Config::default();
    config.set().force_format_strings(true);

    let mut out: Vec<u8> = Vec::new();
    let (summary, file_map, _report) =
        rustfmt::format_input(rustfmt::Input::Text(rust), &config, Some(&mut out)).unwrap();
    assert!(summary.has_no_errors());

    file_map[0].1.to_string()
}

// For these tests, we actually don't verify the token stream word for word.
// Instead we parse the string result into a TokenStream, then stringify _that_
// then verify the result against known code. This is because whitespaces and
// indentation and just plain consistency is hard to maintain.
#[test_generator::test_resources("candid/tests/assets/codegen/*/*.did")]
fn rust_test(resource: &str) {
    let idl_path = std::env::current_dir()
        .unwrap()
        .parent()
        .unwrap()
        .join(Path::new(resource));
    let rust_path = idl_path.with_extension("rs");
    let idl = std::fs::read_to_string(&idl_path).unwrap();
    let expected = std::fs::read_to_string(&rust_path).unwrap();

    let prog = IDLProg::from_str(&idl).unwrap();
    let actual = idl_to_rust(&prog, &candid::codegen::rust::Config::default()).unwrap();

    // Format the actual and the rust strings. Then compare them.
    let actual = run_formatter(actual);
    let expected = run_formatter(expected);

    assert_eq!(actual, expected);
}
