use candid::types::value::{IDLArgs, IDLField, IDLValue, VariantValue};
use candid::types::{Label, TypeEnv};
use candid::{decode_args, decode_one, Decode};
use candid_parser::{parse_idl_args, parse_idl_prog, typing::check_prog};

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
    parse_check("(principal \"w7x7r-cok77-xa\")");
}

#[test]
fn test_typed_parser() {
    let candid = r#"
type List = List1;
type List1 = List2;
type List2 = opt record { head: int16; tail: List1 };
type byte = nat8;
type enum = variant { a: nat; b: text; c };
type f = func (byte, int, nat, int8) -> (List, enum);
service : {
  f : f;
}
"#;
    let ast = parse_idl_prog(candid).unwrap();
    let mut env = TypeEnv::new();
    let actor = check_prog(&mut env, &ast).unwrap().unwrap();
    let method = env.get_method(&actor, "f").unwrap();
    {
        let args = parse_idl_args("(42,42,42,42)").unwrap();
        let encoded = args
            .to_bytes_with_types(
                &env,
                &method
                    .args
                    .iter()
                    .map(|arg| arg.typ.clone())
                    .collect::<Vec<_>>(),
            )
            .unwrap();
        let decoded = IDLArgs::from_bytes(&encoded).unwrap();
        assert_eq!(
            decoded.args,
            vec![
                IDLValue::Nat8(42),
                IDLValue::Int(42.into()),
                IDLValue::Nat(42u32.into()),
                IDLValue::Int8(42),
            ]
        );
    }
    {
        let str = "(opt record { head = 1000; tail = opt record {head = -2000; tail = null}}, variant {a = 42})";
        let args = parse_idl_args(str).unwrap();
        let encoded = args.to_bytes_with_types(&env, &method.rets).unwrap();
        let decoded = IDLArgs::from_bytes(&encoded).unwrap();
        assert_eq!(decoded.to_string(), "(\n  opt record {\n    1_158_359_328 = 1_000 : int16;\n    1_291_237_008 = opt record {\n      1_158_359_328 = -2_000 : int16;\n      1_291_237_008 = null;\n    };\n  },\n  variant { 97 = 42 : nat },\n)");
        let decoded = IDLArgs::from_bytes_with_types(&encoded, &env, &method.rets).unwrap();
        assert_eq!(
            decoded.to_string(),
            "(\n  opt record {\n    head = 1_000 : int16;\n    tail = opt record { head = -2_000 : int16; tail = null };\n  },\n  variant { a = 42 : nat },\n)"
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
    check(Text("Hi ☃\n".to_string()), "4449444c00017107486920e298830a");
    check(Reserved, "4449444c000170");
    check(Blob(vec![1, 2, 3, 4]), "4449444c016d7b01000401020304");
    test_decode(&hex("4449444c016e7c010000"), &None);
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
    let value = Variant(VariantValue(
        Box::new(IDLField {
            id: Label::Id(3_303_859),
            val: Null,
        }),
        0,
    ));
    let bytes = hex("4449444c016b02b3d3c9017fe6fdd5017f010000");
    test_decode(&bytes, &value);
    let encoded = IDLArgs::new(&[value.clone()]).to_bytes().unwrap();
    test_decode(&encoded, &value);
}

fn parse_check(str: &str) {
    let args = parse_idl_args(str).unwrap();
    let encoded = args.to_bytes().unwrap();
    let decoded = IDLArgs::from_bytes(&encoded).unwrap();
    let output = decoded.to_string();
    let back_args = parse_idl_args(&output).unwrap();
    let annotated_args = args
        .annotate_types(true, &TypeEnv::new(), &back_args.get_types())
        .unwrap();
    assert_eq!(annotated_args, back_args);
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
        "\nActual\n{encoded:x?}\nExpected\n{expected:x?}\n"
    );
}

fn test_decode(bytes: &[u8], expected: &IDLValue) {
    let decoded_macro = Decode!(bytes, IDLValue).unwrap();
    let (decoded_fn,): (IDLValue,) = decode_args(bytes).unwrap();
    let decoded_one: IDLValue = decode_one(bytes).unwrap();
    assert_eq!(decoded_macro, *expected);
    assert_eq!(decoded_fn, *expected);
    assert_eq!(decoded_one, *expected);
}

fn int_vec(v: &[i64]) -> IDLValue {
    let vec: Vec<_> = v.iter().map(|n| IDLValue::Int((*n).into())).collect();
    IDLValue::Vec(vec)
}

fn hex(bytes: &str) -> Vec<u8> {
    hex::decode(bytes).unwrap()
}
