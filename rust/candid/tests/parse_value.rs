use candid::parser::typing::TypeEnv;
use candid::parser::value::{IDLArgs, IDLField, IDLValue, VariantValue};
use candid::types::{Label, Type};

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
    let args = parse_args(" (true, null, 42, 42., +42.42, -42e5, 42.42e-5)");
    assert_eq!(
        args.args,
        vec![
            IDLValue::Bool(true),
            IDLValue::Null,
            IDLValue::Number("42".to_owned()),
            IDLValue::Float64(42f64),
            IDLValue::Float64(42.42f64),
            IDLValue::Float64(-42e5f64),
            IDLValue::Float64(42.42e-5f64),
        ]
    );
    assert_eq!(
        format!("{}", args),
        "(true, null, 42, 42, 42.42, -4200000, 0.0004242)"
    );
}

#[test]
fn parse_string_literals() {
    let args = parse_args(r#"("", "\u{10ffff}\n", "\0a\0dd")"#);
    assert_eq!(
        args.args,
        vec![
            IDLValue::Text("".to_owned()),
            IDLValue::Text("\u{10ffff}\n".to_owned()),
            IDLValue::Text("\n\rd".to_owned()),
        ]
    );
    let args = parse_args("(blob \"DIDL\\00\\01\\7d\\80\\00\")");
    assert_eq!(format!("{}", args), r#"(blob "DIDL\00\01}\80\00")"#);
    let args = parse_args_err("(\"DIDL\\00\\01\\7d\\80\\00\")");
    assert_eq!(
        format!("{}", args.unwrap_err()),
        "Candid parser error: Not valid unicode text at 1..22"
    );
    let args = parse_args_err("(\"\\u{d800}\")");
    assert_eq!(
        format!("{}", args.unwrap_err()),
        "Candid parser error: Unicode escape out of range d800 at 2..10"
    );
    let result = parse_args_err("(\"\\q\")");
    assert_eq!(
        format!("{}", result.unwrap_err()),
        "Candid parser error: Unknown escape character q at 2..4"
    );
}

#[test]
fn parse_more_literals() {
    let mut args =
        parse_args("(true, null, 4_2, \"哈哈\", \"string with whitespace\", 0x2a, -42, false)");
    args.args[2] = args.args[2]
        .annotate_type(true, &TypeEnv::new(), &Type::Nat)
        .unwrap();
    args.args[5] = args.args[5]
        .annotate_type(true, &TypeEnv::new(), &Type::Int)
        .unwrap();
    args.args[6] = args.args[6]
        .annotate_type(true, &TypeEnv::new(), &Type::Int)
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
    args.args[0] = args.args[0]
        .annotate_type(true, &TypeEnv::new(), &Type::Vec(Box::new(Type::Nat)))
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
    assert_eq!(format!("{}", args), "(vec { 1; 2; 3; 4 })");
}

#[test]
fn parse_optional_record() {
    let mut args =
        parse_args("(opt record {}, record { 1=42;44=\"test\"; 2=false }, variant { 5=null })");
    let typ = parse_type("record { 1: nat; 44: text; 2: bool }");
    args.args[1] = args.args[1]
        .annotate_type(true, &TypeEnv::new(), &typ)
        .unwrap();
    assert_eq!(
        args.args,
        vec![
            IDLValue::Opt(Box::new(IDLValue::Record(vec![]))),
            IDLValue::Record(vec![
                IDLField {
                    id: Label::Id(1),
                    val: IDLValue::Nat(42.into())
                },
                IDLField {
                    id: Label::Id(2),
                    val: IDLValue::Bool(false)
                },
                IDLField {
                    id: Label::Id(44),
                    val: IDLValue::Text("test".to_owned())
                },
            ]),
            IDLValue::Variant(VariantValue(
                Box::new(IDLField {
                    id: Label::Id(5),
                    val: IDLValue::Null
                }),
                0
            ))
        ]
    );
    assert_eq!(
        format!("{}", args),
        "(opt record {}, record { 1 = 42; 2 = false; 44 = \"test\" }, variant { 5 })"
    );
}

#[test]
fn parse_nested_record() {
    let mut args = parse_args(
        "(record {label=42; 0x2b=record {test=\"test\"; \"opt\"=\"hello\"}; long_label=opt null})",
    );
    let typ = parse_type(
        "record {label: nat; 0x2b:record { test:text; \"opt\":text }; long_label: opt null }",
    );
    args.args[0] = args.args[0]
        .annotate_type(true, &TypeEnv::new(), &typ)
        .unwrap();
    assert_eq!(
        args.args,
        vec![IDLValue::Record(vec![
            IDLField {
                id: Label::Id(43),
                val: IDLValue::Record(vec![
                    IDLField {
                        id: Label::Named("opt".to_owned()),
                        val: IDLValue::Text("hello".to_owned())
                    },
                    IDLField {
                        id: Label::Named("test".to_owned()),
                        val: IDLValue::Text("test".to_owned())
                    }
                ])
            },
            IDLField {
                id: Label::Named("long_label".to_owned()),
                val: IDLValue::Opt(Box::new(IDLValue::Null))
            },
            IDLField {
                id: Label::Named("label".to_owned()),
                val: IDLValue::Nat(42.into())
            }
        ])]
    );
    assert_eq!(format!("{}", args), "(\n  record {\n    43 = record { \"opt\" = \"hello\"; test = \"test\" };\n    long_label = opt null;\n    label = 42;\n  },\n)");
    let skip_typ = parse_type("record { label: nat }");
    args.args[0] = args.args[0]
        .annotate_type(true, &TypeEnv::new(), &skip_typ)
        .unwrap();
    assert_eq!(format!("{}", args), "(record { label = 42 })");
}

#[test]
fn parse_shorthand() {
    let args =
        parse_args("(record { 42; record {}; true; record { 42; 0x2a=42; 42; 42 }; opt 42 })");
    assert_eq!(format!("{}", args), "(\n  record {\n    42;\n    record {};\n    true;\n    record { 0 = 42; 42 = 42; 43 = 42; 44 = 42 };\n    opt 42;\n  },\n)");
    let args = parse_args("(variant { 0x2a }, variant { label })");
    assert_eq!(format!("{}", args), "(variant { 42 }, variant { label })");
}

#[test]
fn parse_annval() {
    let args = parse_args("((1))");
    assert_eq!(
        args,
        IDLArgs {
            args: vec![IDLValue::Number("1".to_string())]
        }
    );
    let args = parse_args("(1 : nat, (123 : int), 456 : int32, 789. : float32, 1011.0 : float64)");
    assert_eq!(
        args,
        IDLArgs {
            args: vec![
                IDLValue::Nat(1.into()),
                IDLValue::Int(123.into()),
                IDLValue::Int32(456),
                IDLValue::Float32(789f32),
                IDLValue::Float64(1011f64)
            ]
        }
    );
    let result = parse_args_err("(vec {1;2;3;-4;5;6;7} : vec nat)");
    assert_eq!(
        format!("{}", result.unwrap_err()),
        "Candid parser error: Cannot parse BigUint at 1..21"
    );
}
