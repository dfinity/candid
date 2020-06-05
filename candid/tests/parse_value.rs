use candid::parser::typing::TypeEnv;
use candid::parser::value::{IDLArgs, IDLField, IDLValue};
use candid::types::Type;

fn parse_args(input: &str) -> IDLArgs {
    input.parse().unwrap()
}

fn parse_args_err(input: &str) -> candid::Result<IDLArgs> {
    input.parse()
}

fn parse_type(input: &str) -> Type {
    use candid::parser::types::IDLType;
    let env = TypeEnv::new();
    let ast = input.parse::<IDLType>().unwrap();
    env.ast_to_type(&ast).unwrap()
}

#[test]
fn parse_bool_lit() {
    let args = parse_args("(true)");
    assert_eq!(args.args, vec![IDLValue::Bool(true)]);
    assert_eq!(format!("{}", args), "(true)");
}

#[test]
fn parse_literals() {
    let args = parse_args(" (true, null )");
    assert_eq!(args.args, vec![IDLValue::Bool(true), IDLValue::Null]);
    assert_eq!(format!("{}", args), "(true, null)");
}

#[test]
fn parse_string_literals() {
    let args = parse_args("(\"\", \"\\u{10ffff}\\n\", \"\\0a\\0dd\")");
    assert_eq!(
        args.args,
        vec![
            IDLValue::Text("".to_owned()),
            IDLValue::Text("\u{10ffff}\n".to_owned()),
            IDLValue::Text("\n\rd".to_owned()),
        ]
    );
    let args = parse_args_err("(\"\\u{d800}\")");
    assert_eq!(
        format!("{}", args.unwrap_err()),
        "IDL parser error: Unicode escape out of range d800"
    );
    let result = parse_args_err("(\"\\q\")");
    assert_eq!(
        format!("{}", result.unwrap_err()),
        "IDL parser error: Unexpected character q"
    );
}

#[test]
fn parse_more_literals() {
    let mut args =
        parse_args("(true, null, 4_2, \"哈哈\", \"string with whitespace\", 0x2a, -42, false)");
    args.annotate_type(2, &TypeEnv::new(), &Type::Nat)
        .unwrap()
        .annotate_type(5, &TypeEnv::new(), &Type::Int)
        .unwrap()
        .annotate_type(6, &TypeEnv::new(), &Type::Int)
        .unwrap();
    assert_eq!(
        args.args,
        vec![
            IDLValue::Bool(true),
            IDLValue::Null,
            IDLValue::Nat(42.into()),
            IDLValue::Text("哈哈".to_owned()),
            IDLValue::Text("string with whitespace".to_owned()),
            IDLValue::Int(42.into()),
            IDLValue::Int((-42).into()),
            IDLValue::Bool(false)
        ]
    );
    assert_eq!(
        format!("{}", args),
        "(true, null, 42, \"哈哈\", \"string with whitespace\", 42, -42, false)"
    );
}

#[test]
fn parse_vec() {
    let mut args = parse_args("(vec{1;2;3;4})");
    args.annotate_types(&TypeEnv::new(), &[Type::Vec(Box::new(Type::Nat))])
        .unwrap();
    assert_eq!(
        args.args,
        vec![IDLValue::Vec(vec![
            IDLValue::Nat(1.into()),
            IDLValue::Nat(2.into()),
            IDLValue::Nat(3.into()),
            IDLValue::Nat(4.into())
        ])]
    );
    assert_eq!(format!("{}", args), "(vec { 1; 2; 3; 4; })");
}

#[test]
fn parse_optional_record() {
    let mut args =
        parse_args("(opt record {}, record { 1=42;44=\"test\"; 2=false }, variant { 5=null })");
    let typ = parse_type("record { 1: nat; 44: text; 2: bool }");
    args.annotate_type(1, &TypeEnv::new(), &typ).unwrap();
    assert_eq!(
        args.args,
        vec![
            IDLValue::Opt(Box::new(IDLValue::Record(vec![]))),
            IDLValue::Record(vec![
                IDLField {
                    id: 1,
                    val: IDLValue::Nat(42.into())
                },
                IDLField {
                    id: 2,
                    val: IDLValue::Bool(false)
                },
                IDLField {
                    id: 44,
                    val: IDLValue::Text("test".to_owned())
                },
            ]),
            IDLValue::Variant(Box::new(IDLField {
                id: 5,
                val: IDLValue::Null
            }))
        ]
    );
    assert_eq!(
        format!("{}", args),
        "(opt record { }, record { 1 = 42; 2 = false; 44 = \"test\"; }, variant { 5 = null })"
    );
}

#[test]
fn parse_nested_record() {
    let mut args = parse_args(
        "(record {label=42; 0x2b=record {test=\"test\"; msg=\"hello\"}; long_label=opt null})",
    );
    let typ = parse_type(
        "record {label: nat; 0x2b:record { test:text; msg:text }; long_label: opt null }",
    );
    args.annotate_type(0, &TypeEnv::new(), &typ).unwrap();
    assert_eq!(
        args.args,
        vec![IDLValue::Record(vec![
            IDLField {
                id: 43,
                val: IDLValue::Record(vec![
                    IDLField {
                        id: 5_446_209,
                        val: IDLValue::Text("hello".to_owned())
                    },
                    IDLField {
                        id: 1_291_438_162,
                        val: IDLValue::Text("test".to_owned())
                    }
                ])
            },
            IDLField {
                id: 1_350_385_585,
                val: IDLValue::Opt(Box::new(IDLValue::Null))
            },
            IDLField {
                id: 1_873_743_348,
                val: IDLValue::Nat(42.into())
            }
        ])]
    );
    assert_eq!(format!("{}", args), "(record { 43 = record { 5446209 = \"hello\"; 1291438162 = \"test\"; }; 1350385585 = opt null; 1873743348 = 42; })");
}

#[test]
fn parse_shorthand() {
    let args =
        parse_args("(record { 42; record {}; true; record { 42; 0x2a=42; 42; 42 }; opt 42 })");
    assert_eq!(format!("{}", args), "(record { 0 = 42; 1 = record { }; 2 = true; 3 = record { 0 = 42; 42 = 42; 43 = 42; 44 = 42; }; 4 = opt 42; })");
    let args = parse_args("(variant { 0x2a }, variant { label })");
    assert_eq!(
        format!("{}", args),
        "(variant { 42 = null }, variant { 1873743348 = null })"
    );
}
