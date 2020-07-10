use candid::parser::{
    types::IDLProg,
    typing::{check_prog, TypeEnv},
    value::{IDLArgs, IDLField, IDLValue},
};
use candid::types::Label;
use candid::Decode;

#[test]
fn test_parser() {
    parse_check("(true,42,+42,-42)");
    parse_check("(\"test\", variant {5})");
    parse_check("(opt null, record {}, vec{1;2;3})");
    parse_check("(record {1=42;44=\"test\";2=false})");
    parse_check("(record {label=42; 43=record {test100=\"test\"; \"标签\"=\"hello\"}; long_label=opt null}, variant {C})");
    parse_check("(record { record{ 42; opt 42 }; vec{4;5;6} })");
    parse_check("(variant { A=opt 42 }, variant {A=vec{1;2;3}})");
    parse_check(
        "(variant { cons=record{ 42; variant { cons=record{43; variant { nil=record{} }} } } })",
    );
    parse_check("(principal \"ic:caffee59\")");
}

#[test]
fn test_typed_parser() {
    let candid = r#"
type List = List1;
type List1 = List2;
type List2 = opt record { head: nat8; tail: List1 };
type byte = nat8;
type f = func (byte, int, nat, int8) -> (List);
service : {
  f : f;
}
"#;
    let ast = candid.parse::<IDLProg>().unwrap();
    let mut env = TypeEnv::new();
    let actor = check_prog(&mut env, &ast).unwrap().unwrap();
    let method = env.get_method(&actor, "f").unwrap();
    {
        let args = "(42,42,42,42)".parse::<IDLArgs>().unwrap();
        let encoded = args.to_bytes_with_types(&env, &method.args).unwrap();
        let decoded = IDLArgs::from_bytes(&encoded).unwrap();
        assert_eq!(
            decoded.args,
            vec![
                IDLValue::Nat8(42),
                IDLValue::Int(42.into()),
                IDLValue::Nat(42.into()),
                IDLValue::Int8(42)
            ]
        );
    }
    {
        let str = "(opt record { head = 1; tail = opt record {head = 2; tail = null}})";
        let args = str.parse::<IDLArgs>().unwrap();
        let encoded = args.to_bytes_with_types(&env, &method.rets).unwrap();
        let decoded = IDLArgs::from_bytes(&encoded).unwrap();
        assert_eq!(decoded.to_string(), "(opt record { 1158359328 = 1; 1291237008 = opt record { 1158359328 = 2; 1291237008 = null; }; })");
        let decoded = IDLArgs::from_bytes_with_types(&encoded, &env, &method.rets).unwrap();
        assert_eq!(
            decoded.to_string(),
            "(opt record { head = 1; tail = opt record { head = 2; tail = null; }; })"
        );
        let decoded = IDLArgs::from_bytes_with_types(&encoded, &env, &[]).unwrap();
        assert_eq!(decoded.to_string(), "()");
    }
}

#[test]
fn test_value() {
    use IDLValue::*;
    check(Bool(true), "4449444c00017e01");
    check(Int(1_234_567_890.into()), "4449444c00017cd285d8cc04");
    check(Opt(Box::new(Int(42.into()))), "4449444c016e7c0100012a");
    //check(Null, "4449444c016e7c010000");
    check(Text("Hi ☃\n".to_string()), "4449444c00017107486920e298830a");
    check(int_vec(&[0, 1, 2, 3]), "4449444c016d7c01000400010203");
    check(
        Record(vec![
            IDLField {
                id: Label::Id(0),
                val: Int(42.into()),
            },
            IDLField {
                id: Label::Id(1),
                val: Text("💩".to_string()),
            },
        ]),
        "4449444c016c02007c017101002a04f09f92a9",
    );
    check(
        Record(vec![
            IDLField {
                id: Label::Id(4_895_187),
                val: Bool(true),
            },
            IDLField {
                id: Label::Id(5_097_222),
                val: Int(42.into()),
            },
        ]),
        "4449444c016c02d3e3aa027e868eb7027c0100012a",
    );
}

#[test]
fn test_variant() {
    use IDLValue::*;
    let value = Variant(
        Box::new(IDLField {
            id: Label::Id(3_303_859),
            val: Null,
        }),
        0,
    );
    let bytes = hex("4449444c016b02b3d3c9017fe6fdd5017f010000");
    test_decode(&bytes, &value);
    let encoded = IDLArgs::new(&[value.clone()]).to_bytes().unwrap();
    test_decode(&encoded, &value);
}

fn parse_check(str: &str) {
    let args = str.parse::<IDLArgs>().unwrap();
    let encoded = args.to_bytes().unwrap();
    let decoded = IDLArgs::from_bytes(&encoded).unwrap();
    let output = decoded.to_string();
    let back_args = output.parse::<IDLArgs>().unwrap();
    assert_eq!(args, back_args);
}

fn check(v: IDLValue, bytes: &str) {
    let bytes = hex(bytes);
    test_decode(&bytes, &v);
    test_encode(&v, &bytes);
}

fn test_encode(v: &IDLValue, expected: &[u8]) {
    let args = IDLArgs::new(&[v.clone()]);
    let encoded = args.to_bytes().unwrap();
    assert_eq!(
        encoded, expected,
        "\nActual\n{:x?}\nExpected\n{:x?}\n",
        encoded, expected
    );
}

fn test_decode(bytes: &[u8], expected: &IDLValue) {
    let decoded = Decode!(bytes, IDLValue).unwrap();
    assert_eq!(decoded, *expected);
}

fn int_vec(v: &[i64]) -> IDLValue {
    let vec: Vec<_> = v.iter().map(|n| IDLValue::Int((*n).into())).collect();
    IDLValue::Vec(vec)
}

fn hex(bytes: &str) -> Vec<u8> {
    hex::decode(bytes).unwrap()
}
