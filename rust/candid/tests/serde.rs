use candid::{
    decode_one_with_config, encode_one, CandidType, Decode, DecoderConfig, Deserialize, Encode,
    Int, Nat,
};
use candid_parser::utils::check_rust_type;

#[test]
fn test_error() {
    check_error(|| test_decode(b"DID", &42), "io error");
    check_error(|| test_decode(b"DIDL", &42), "len at byte offset 4");
    check_error(
        || test_decode(b"DIDL\0\0", &42),
        "No more values on the wire",
    );
    check_error(
        || test_decode(b"DIDL\x01\x7c", &42),
        "not a valid future type at byte offset 5",
    );
    // Infinite loop are prevented by design
    check_error(
        || test_decode(b"DIDL\x02\x6e\x01\0", &42),
        "not a valid future type at byte offset 7",
    );
    check_error(
        || test_decode(b"DIDL\0\x01\x7e\x01\x01", &true),
        "Trailing value after finishing deserialization",
    );
    check_error(|| test_decode(b"DIDL\0\x01\x7e", &true), "io error");
    // Out of bounds type index
    check_error(
        || test_decode(b"DIDL\0\x01\0\x01", &42),
        "type index 0 out of range",
    );
    check_error_or(
        || {
            test_decode(b"DIDL\x02\x6c\x01\x0a\x01\x6d\x00\x01\x01                                                                                                                                                                                                                                                                                                                                                                                                                                                                    ", &candid::Reserved)
        },
        // Depending on stack size, we either reach recursion limit or skipping limit
        "Recursion limit exceeded",
        "Skipping cost exceeds the limit",
    );
}

#[test]
fn test_bool() {
    all_check(true, "4449444c00017e01");
    all_check(false, "4449444c00017e00");
}

#[test]
fn test_integer() {
    all_check(Int::from(42), "4449444c00017c2a");
    all_check(Nat::from(42u16), "4449444c00017d2a");
    all_check(Int::from(1_234_567_890), "4449444c00017cd285d8cc04");
    all_check(Nat::from(1_234_567_890u64), "4449444c00017dd285d8cc04");
    all_check(Nat::from(5_000_000_000u64), "4449444c00017d80e497d012");
    all_check(Int::from(-1_234_567_890), "4449444c00017caefaa7b37b");
    all_check(Box::new(Int::from(42)), "4449444c00017c2a");
    all_check(
        Int::parse(b"60000000000000000").unwrap(),
        "4449444c00017c808098f4e9b5caea00",
    );
    all_check(
        Nat::parse(b"60000000000000000").unwrap(),
        "4449444c00017d808098f4e9b5ca6a",
    );
    test_decode(
        &hex("4449444c00017d808098f4e9b5ca6a"),
        &Int::parse(b"60000000000000000").unwrap(),
    );
    all_check(
        Int::parse(b"-60000000000000000").unwrap(),
        "4449444c00017c8080e88b96cab5957f",
    );
    check_error(|| test_decode(&hex("4449444c00017c2a"), &42i64), "Int64");
}

#[test]
fn test_fixed_number() {
    all_check(42u8, "4449444c00017b2a");
    all_check(42u16, "4449444c00017a2a00");
    all_check(42u32, "4449444c0001792a000000");
    all_check(42u64, "4449444c0001782a00000000000000");
    all_check(42usize, "4449444c0001782a00000000000000");
    all_check(42u128, "4449444c00017d2a");
    all_check(42i8, "4449444c0001772a");
    all_check(42i16, "4449444c0001762a00");
    all_check(42i32, "4449444c0001752a000000");
    all_check(42i64, "4449444c0001742a00000000000000");
    all_check(-42i64, "4449444c000174d6ffffffffffffff");
    all_check(-42isize, "4449444c000174d6ffffffffffffff");
    all_check(42i128, "4449444c00017c2a");
    test_decode(&hex("4449444c00017d2a"), &42i128);
}

#[test]
fn test_float() {
    all_check(3f32, "4449444c00017300004040");
    all_check(3f64, "4449444c0001720000000000000840");
    all_check(6f64, "4449444c0001720000000000001840");
    all_check(0.5, "4449444c000172000000000000e03f");
    all_check(-0.5, "4449444c000172000000000000e0bf");
}

#[test]
fn test_text() {
    all_check("Hi ☃\n".to_string(), "4449444c00017107486920e298830a");
    let bytes = hex("4449444c00017107486920e298830a");
    test_encode(&"Hi ☃\n", &bytes);
    test_decode(&bytes, &"Hi ☃\n");
    test_decode(&bytes, &std::borrow::Cow::from("Hi ☃\n"));
}

#[test]
fn test_time() {
    use std::time::{Duration, SystemTime};
    let now = SystemTime::now();
    let duration = now.duration_since(SystemTime::UNIX_EPOCH).unwrap();
    let encoded = Encode!(&now).unwrap();
    let decoded = Decode!(&encoded, SystemTime).unwrap();
    assert_eq!(now, decoded);
    let encoded = Encode!(&duration).unwrap();
    let decoded = Decode!(&encoded, Duration).unwrap();
    assert_eq!(duration, decoded);
}

#[test]
fn test_reserved() {
    use candid::{Empty, Reserved};
    all_check(Reserved, "4449444c000170");
    test_decode(&hex("4449444c00017c2a"), &candid::Reserved);
    test_decode(
        &hex("4449444c016c02d3e3aa027e868eb7027c0100012a"),
        &candid::Reserved,
    );
    let res: Result<u8, Empty> = Ok(1);
    all_check(res, "4449444c016b02bc8a017bc5fed2016f01000001");
    let bytes = hex("4449444c016b02bc8a017bc5fed2016f010001");
    check_error(
        || Decode!(&bytes, Result<u8, Empty>).unwrap(),
        "Cannot decode empty type",
    );
}

#[test]
fn test_reference() {
    use candid::{define_function, define_service, func, Principal};
    let principal = Principal::from_text("w7x7r-cok77-xa").unwrap();
    all_check(principal, "4449444c0001680103caffee");
    define_function!(CustomFunc: () -> (candid::Nat));
    all_check(
        CustomFunc::new(principal, "method".to_owned()),
        "4449444c016a00017d000100010103caffee066d6574686f64",
    );
    let bytes = hex("4449444c016a00017f000100010100016d");
    test_decode(&bytes, &None::<CustomFunc>);
    define_service!(MyService: { "g": func!(() -> () query); "f": CustomFunc::ty() });
    all_check(
        MyService::new(principal),
        "4449444c0369020166010167026a00017d006a0000010101000103caffee",
    );
    define_service!(S: { "next" : func!(() -> (S)) });
    let v = S::new(principal);
    assert_eq!(v, Decode!(&Encode!(&v).unwrap(), S).unwrap());
}

#[test]
fn test_option() {
    all_check(Some(Int::from(42)), "4449444c016e7c0100012a");
    all_check(Some(Some(Int::from(42))), "4449444c026e016e7c010001012a");
    // Deserialize None of type Option<i32> to Option<String>
    let none_i32: Option<i32> = None;
    let none_str: Option<String> = None;
    let bytes = encode(&none_i32);
    test_decode(&bytes, &none_str);
    all_check(none_i32, "4449444c016e75010000");
    // Deserialize \mu T.Option<T> to a non-recursive type
    let v: Option<Option<Option<i32>>> = Some(Some(None));
    test_decode(b"DIDL\x01\x6e\0\x01\0\x01\x01\0", &v);
    // special opt rule
    #[derive(CandidType, Deserialize, PartialEq, Debug)]
    struct A {
        canister_id: Option<candid::Principal>,
    }
    #[derive(CandidType, Deserialize, PartialEq, Debug)]
    struct B {
        canister_id: Option<i32>,
    }
    let bytes = encode(&B {
        canister_id: Some(42),
    });
    let expected = A { canister_id: None };
    test_decode(&bytes, &expected);
}

#[test]
fn test_struct() {
    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    struct A1 {
        foo: Int,
        bar: bool,
    }
    let a1 = A1 {
        foo: 42.into(),
        bar: true,
    };
    all_check(a1, "4449444c016c02d3e3aa027e868eb7027c0100012a");

    // Field name hash is larger than u32
    check_error(
        || {
            test_decode(
                &hex("4449444c016c02a3e0d4b9bf86027e868eb7027c0100012a"),
                &A1 {
                    foo: 42.into(),
                    bar: true,
                },
            )
        },
        "field id out of 32-bit range",
    );

    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    struct A11 {
        foo: Int,
        bar: bool,
        baz: A1,
    }
    all_check(
        A11 {
            foo: 42.into(),
            bar: true,
            baz: A1 {
                foo: 10.into(),
                bar: false,
            },
        },
        "4449444c026c03d3e3aa027edbe3aa0201868eb7027c6c02d3e3aa027e868eb7027c010001000a2a",
    );

    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    struct B(bool, Int);
    all_check(B(true, 42.into()), "4449444c016c02007e017c0100012a");

    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    struct List {
        head: Int,
        tail: Option<Box<List>>,
    }

    let list = List {
        head: 42.into(),
        tail: Some(Box::new(List {
            head: 43.into(),
            tail: None,
        })),
    };
    all_check(
        list,
        "4449444c026c02a0d2aca8047c90eddae704016e0001002a012b00",
    );

    let list: Option<List> = None;
    // with memoization on the unrolled type, type table will have 2 entries.
    // all_check(list, "4449444c026e016c02a0d2aca8047c90eddae70400010000");
    all_check(list, "4449444c036e016c02a0d2aca8047c90eddae704026e01010000");
    check_rust_type::<List>("type List = record {head: int; tail: opt List}; (List)").unwrap();
    check_rust_type::<List>("type T = record {head: int; tail: opt T}; (T)").unwrap();
}

#[test]
fn optional_fields() {
    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    struct OldStruct {
        bar: bool,
        baz: Option<Old>,
    }
    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    enum Old {
        Foo,
        Bar(bool),
    }
    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    enum New {
        Foo,
        Bar(bool),
        Baz(bool),
    }
    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    struct NewStruct {
        foo: Option<u8>,
        bar: bool,
        baz: Option<New>,
    }
    check_rust_type::<NewStruct>(
        "(record { foo: opt nat8; bar: bool; baz: opt variant { Foo; Bar: bool; Baz: bool }})",
    )
    .unwrap();
    let bytes = encode(&OldStruct {
        bar: true,
        baz: Some(Old::Foo),
    });
    test_decode(
        &bytes,
        &NewStruct {
            foo: None,
            bar: true,
            baz: Some(New::Foo),
        },
    );
    let bytes = encode(&NewStruct {
        foo: Some(42),
        bar: false,
        baz: Some(New::Baz(true)),
    });
    test_decode(
        &bytes,
        &OldStruct {
            bar: false,
            baz: None,
        },
    );
    let bytes = encode(&New::Baz(false));
    check_error(
        || test_decode(&bytes, &Old::Bar(false)),
        "Unknown variant field",
    );
}

#[test]
fn test_equivalent_types() {
    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    struct RootType {
        typeas: Vec<TypeA>,
    }
    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    struct TypeA {
        typeb: Box<Option<TypeB>>,
    }
    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    struct TypeB {
        typea: Option<TypeA>,
    }
    check_rust_type::<RootType>(
        r#"
type A = record { typeb: opt B };
type B = record { typea: opt A };
(record { typeas: vec A })"#,
    )
    .unwrap();
    // Encode to the following types leads to equivalent but different representations of TypeA
    all_check(
        RootType { typeas: Vec::new() },
        "4449444c066c01acd4dbb905016d026c01e8e0add601036e046c01e7e0add601056e02010000",
    );
    all_check(
        TypeB { typea: None },
        "4449444c046c01e7e0add601016e026c01e8e0add601036e00010000",
    );
    Encode!(
        &RootType { typeas: Vec::new() },
        &TypeB { typea: None },
        &TypeA {
            typeb: Box::new(None)
        }
    )
    .unwrap();
}

#[test]
fn test_extra_fields() {
    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    struct A1 {
        foo: i32,
        bar: bool,
    }
    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    enum E1 {
        Foo,
        Bar,
    }
    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    struct A2 {
        foo: i32,
        bar: bool,
        baz: u32,
        bbb: u32,
        bib: E1,
        bab: A1,
    }
    let a1 = A1 { foo: 42, bar: true };
    let a2 = A2 {
        foo: 42,
        bar: true,
        baz: 1,
        bbb: 1,
        bib: E1::Foo,
        bab: A1 {
            foo: 10,
            bar: false,
        },
    };
    // Decode A2 to A1
    let bytes = encode(&a2);
    test_decode(&bytes, &a1);
    // Cannot Decode A1 to A2
    let bytes = encode(&a1);
    check_error(|| test_decode(&bytes, &a2), "field bab");

    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    enum E2 {
        Foo,
        Bar,
        Baz,
    }
    let bytes = encode(&E1::Foo);
    test_decode(&bytes, &E2::Foo);

    let bytes = encode(&E2::Foo);
    test_decode(&bytes, &Some(E2::Foo));
    test_decode(&bytes, &E1::Foo);
}

#[test]
fn test_newtype() {
    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    struct X(i32);
    all_check(X(42), "4449444c0001752a000000");

    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    enum Y {
        A(i32),
    }
    all_check(Y::A(42), "4449444c016b0141750100002a000000");
}

#[test]
#[cfg(feature = "serde_bytes")]
fn test_serde_bytes() {
    use serde_bytes::ByteBuf;
    all_check(
        ByteBuf::from(vec![1u8, 2u8, 3u8]),
        "4449444c016d7b010003010203",
    );
    #[derive(CandidType, Deserialize, Debug, PartialEq)]
    struct Efficient<'a> {
        #[serde(with = "serde_bytes")]
        b: &'a [u8],
        #[serde(with = "serde_bytes")]
        c: Vec<u8>,
    }
    let vec = Efficient {
        b: &[1, 2, 3],
        c: vec![1, 2, 3],
    };
    test_encode(&vec, &hex("4449444c026c02620163016d7b01000301020303010203"));
    test_decode(&hex("4449444c026c02620163016d7b01000301020303010203"), &vec);
    // test cost
    let bytes = hex("4449444c016d7b010003010203");
    let config = get_config();
    let cost = Decode!(@Debug [config]; &bytes, ByteBuf).unwrap().1;
    assert_eq!(cost.decoding_quota, Some(41)); // header cost 9 * 4 + 1 + 4
}

#[test]
#[cfg(feature = "serde_bytes")]
fn test_rc_bytes() {
    use serde_bytes::ByteBuf;
    use std::rc::Rc;
    use std::sync::Arc;

    #[derive(CandidType, Deserialize, PartialEq, Debug)]
    struct RcBytes(#[serde(with = "candid::rc")] Rc<ByteBuf>);
    #[derive(CandidType, Deserialize, PartialEq, Debug)]
    struct ArcBytes(#[serde(with = "candid::arc")] Arc<ByteBuf>);

    all_check(
        RcBytes(Rc::new(ByteBuf::from(vec![1u8, 2u8, 3u8]))),
        "4449444c016d7b010003010203",
    );
    all_check(
        ArcBytes(Arc::new(ByteBuf::from(vec![1u8, 2u8, 3u8]))),
        "4449444c016d7b010003010203",
    );
}

#[test]
fn test_keyword_label() {
    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    struct A {
        r#return: Vec<u8>,
    }
    all_check(
        A {
            r#return: vec![1, 2, 3],
        },
        "4449444c026c01b0c9b649016d7b010003010203",
    );
    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    struct B {
        #[serde(rename = "return")]
        dontcare: Vec<u8>,
    }
    all_check(
        B {
            dontcare: vec![1, 2, 3],
        },
        "4449444c026c01b0c9b649016d7b010003010203",
    );
    #[allow(non_camel_case_types)]
    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    enum E {
        r#return,
    }
    all_check(E::r#return, "4449444c016b01b0c9b6497f010000");
    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    enum E2 {
        #[serde(rename = "return")]
        Dontcare,
    }
    all_check(E2::Dontcare, "4449444c016b01b0c9b6497f010000");
}

#[test]
fn test_mutual_recursion() {
    type List = Option<ListA>;
    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    struct ListA {
        head: Int,
        tail: Box<List>,
    }

    let list: List = None;
    all_check(list, "4449444c026e016c02a0d2aca8047c90eddae70400010000");
}

#[test]
fn test_vector() {
    let vec: Vec<Int> = [0, 1, 2, 3].iter().map(|x| Int::from(*x)).collect();
    all_check(vec, "4449444c016d7c01000400010203");
    all_check(
        [Int::from(0), Int::from(1), Int::from(2), Int::from(3)],
        "4449444c016d7c01000400010203",
    );
    let boxed_array: Box<[Int]> = Box::new([0.into(), 1.into(), 2.into(), 3.into()]);
    all_check(boxed_array, "4449444c016d7c01000400010203");
    all_check(
        [(Int::from(42), "text".to_string())],
        "4449444c026d016c02007c01710100012a0474657874",
    );
    all_check([[[[()]]]], "4449444c046d016d026d036d7f010001010101");
    // Space bomb!
    all_check(vec![(); 1000], "4449444c016d7f0100e807");
    let bytes = hex("4449444c036c01d6fca702016d026c00010080ade204");
    check_error(
        || test_decode(&bytes, &candid::Reserved),
        "Skipping cost exceeds the limit",
    );
    let bytes = hex("4449444c176c02017f027f6c02010002006c02000101016c02000201026c02000301036c02000401046c02000501056c02000601066c02000701076c02000801086c02000901096c02000a010a6c02000b010b6c02000c010c6c02000d020d6c02000e010e6c02000f010f6c02001001106c02001101116c02001201126c02001301136e146d150116050101010101");
    check_error(
        || test_decode(&bytes, &candid::Reserved),
        "Skipping cost exceeds the limit",
    );
}

#[test]
fn test_collection() {
    use std::collections::{BTreeMap, BTreeSet, HashMap};
    let map: HashMap<_, _> = vec![("a".to_string(), 1)].into_iter().collect();
    all_check(map, "4449444c026d016c0200710175010001016101000000");
    let bmap: BTreeMap<_, _> = vec![(1, 101), (2, 102), (3, 103)].into_iter().collect();
    all_check(
        bmap,
        "4449444c026d016c0200750175010003010000006500000002000000660000000300000067000000",
    );
    let bset: BTreeSet<_> = vec![1, 2, 3].into_iter().collect();
    all_check(bset, "4449444c016d75010003010000000200000003000000");
}

#[test]
fn test_tuple() {
    all_check(
        (Int::from(42), "💩".to_string()),
        "4449444c016c02007c017101002a04f09f92a9",
    );
    check_rust_type::<(Int, String)>("(record {int; text})").unwrap();
    let none: Option<String> = None;
    let bytes =
        hex("4449444c046c04007c017e020103026d7c6e036c02a0d2aca8047c90eddae7040201002b010302030400");
    test_decode(
        &bytes,
        &(
            Int::from(43),
            true,
            [Int::from(2), Int::from(3), Int::from(4)],
            none,
        ),
    );
    check_error(
        || {
            test_decode(
                &hex("4449444c016c02007c027101002a04f09f92a9"),
                &(Int::from(42), "💩"),
            )
        },
        "is not a tuple type",
    );
}

#[test]
fn test_variant() {
    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    enum Unit {
        Foo,
        Bar,
    }
    all_check(Unit::Bar, "4449444c016b02b3d3c9017fe6fdd5017f010000");
    check_error(
        || test_decode(&hex("4449444c016b02b3d3c9017fe6fdd5017f010003"), &Unit::Bar),
        "Variant index 3 larger than length 2",
    );

    check_error(
        || test_decode(&hex("4449444c016b02b4d3c9017fe6fdd5017f010000"), &Unit::Bar),
        "Unknown variant field 3_303_860",
    );

    let res: Result<String, String> = Ok("good".to_string());
    all_check(res, "4449444c016b02bc8a0171c5fed2017101000004676f6f64");

    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    enum E {
        Foo,
        Bar(bool, Int),
        Baz { a: Int, b: Nat },
    }

    let v = E::Bar(true, 42.into());
    all_check(
        v,
        "4449444c036b03b3d3c90101bbd3c90102e6fdd5017f6c02007e017c6c02617c627d010000012a",
    );

    let bytes = encode(&Some(E::Foo));
    test_decode(&bytes, &Some(Unit::Foo));
    let bytes = encode(&E::Baz {
        a: 42.into(),
        b: 42u8.into(),
    });
    test_decode(&bytes, &None::<Unit>);
    let bytes = encode(&E::Bar(true, 42.into()));
    test_decode(&bytes, &None::<Unit>);
    check_error(|| test_decode(&bytes, &Unit::Bar), "Subtyping error");

    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    enum T {
        A(),
        B {},
        C,
    }
    all_check(T::A(), "4449444c026b0341014201437f6c00010000");
}

#[test]
fn test_field_rename() {
    #[derive(CandidType, Deserialize, PartialEq, Debug)]
    struct S {
        #[serde(rename = "a")]
        field1: i8,
        #[serde(rename(serialize = "b", deserialize = "b"))]
        field2: u8,
    }
    let v = S {
        field1: 42,
        field2: 42,
    };
    all_check(v, "4449444c016c026177627b01002a2a");

    #[derive(CandidType, Deserialize, PartialEq, Debug)]
    enum E1 {
        #[serde(rename = "a")]
        Field1,
        #[serde(rename(serialize = "b", deserialize = "b"))]
        Field2,
    }
    let v = E1::Field2;
    all_check(v, "4449444c016b02617f627f010001");
    #[derive(CandidType, Deserialize, PartialEq, Debug)]
    enum E2 {
        #[serde(rename = "1-2 + 3")]
        A(i8),
        #[serde(rename = "a-b")]
        B(u8),
    }
    check_rust_type::<E2>(r#"(variant { "1-2 + 3": int8; "a-b": nat8 })"#).unwrap();
    all_check(E2::A(42), "4449444c016b02b684a7027bb493ee970d770100012a");
    #[derive(CandidType, Deserialize, PartialEq, Debug)]
    struct S2 {
        #[serde(rename = "1-2 + 3")]
        a: i8,
        #[serde(rename = "a-b")]
        b: u8,
    }
    all_check(
        S2 { a: 42, b: 42 },
        "4449444c016c02b684a7027bb493ee970d7701002a2a",
    );
}

#[test]
fn test_generics() {
    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    struct G<T, E> {
        g1: T,
        g2: E,
    }
    check_rust_type::<G<i32, bool>>("(record {g1: int32; g2: bool})").unwrap();
    let res = G {
        g1: Int::from(42),
        g2: true,
    };
    all_check(res, "4449444c016c02eab3017cebb3017e01002a01")
}

#[test]
fn test_multiargs() {
    let bytes = Encode!().unwrap();
    assert_eq!(bytes, b"DIDL\0\0");
    Decode!(&bytes).unwrap();

    let bytes = Encode!(
        &Int::from(42),
        &Some(Int::from(42)),
        &Some(Int::from(1)),
        &Some(Int::from(2))
    )
    .unwrap();
    assert_eq!(bytes, hex("4449444c016e7c047c0000002a012a01010102"));

    let (a, b, c, d) = Decode!(&bytes, Int, Option<Int>, Option<Int>, Option<Int>).unwrap();
    assert_eq!(a, 42);
    assert_eq!(b, Some(42.into()));
    assert_eq!(c, Some(1.into()));
    assert_eq!(d, Some(2.into()));

    // okay to decode fewer values from the message
    assert_eq!(Decode!(&bytes, Int).unwrap(), 42);

    let bytes = Encode!(&[(Int::from(42), "text")], &(Int::from(42), "text")).unwrap();
    assert_eq!(
        bytes,
        hex("4449444c026d016c02007c0171020001012a04746578742a0474657874")
    );

    let tuple = Decode!(&bytes, Vec<(Int, &str)>, (Int, String)).unwrap();
    assert_eq!(tuple.0, [(42.into(), "text")]);
    assert_eq!(tuple.1, (42.into(), "text".to_string()));

    let tuple = Decode!(
        &bytes,
        Vec<(Int, &str)>,
        (Int, String),
        Option<i32>,
        (),
        candid::Reserved
    )
    .unwrap();
    assert_eq!(tuple.2, None);
    #[allow(clippy::unit_cmp)]
    {
        assert_eq!(tuple.3, ());
    }
    assert_eq!(tuple.4, candid::Reserved);
}

fn hex(bytes: &str) -> Vec<u8> {
    hex::decode(bytes).unwrap()
}

fn all_check<T>(value: T, bytes: &str)
where
    T: PartialEq + CandidType + serde::de::DeserializeOwned + std::fmt::Debug,
{
    let bytes = hex(bytes);
    test_encode(&value, &bytes);
    test_decode(&bytes, &value);
}

fn test_encode<T>(value: &T, expected: &[u8])
where
    T: CandidType,
{
    let encoded = encode(&value);
    assert_eq!(
        encoded, expected,
        "\nActual\n{encoded:02x?}\nExpected\n{expected:02x?}\n"
    );
}

fn get_config() -> DecoderConfig {
    let mut config = DecoderConfig::new();
    config
        .set_decoding_quota(20_000_000)
        .set_skipping_quota(10_000);
    config
}

fn test_decode<'de, T>(bytes: &'de [u8], expected: &T)
where
    T: PartialEq + serde::de::Deserialize<'de> + std::fmt::Debug + CandidType,
{
    let config = get_config();
    let decoded_one = decode_one_with_config::<T>(bytes, &config).unwrap();
    let decoded_macro = Decode!([config]; bytes, T).unwrap();
    assert_eq!(decoded_one, *expected);
    assert_eq!(decoded_macro, *expected);
}

fn encode<T: CandidType>(value: &T) -> Vec<u8> {
    let encode_one = encode_one(value).unwrap();
    let encode_macro = Encode!(&value).unwrap();

    assert_eq!(encode_one, encode_macro);
    encode_one
}

fn check_error<F: FnOnce() -> R + std::panic::UnwindSafe, R>(f: F, str: &str) {
    assert_eq!(
        std::panic::catch_unwind(f)
            .err()
            .and_then(|a| a.downcast_ref::<String>().map(|s| { s.contains(str) })),
        Some(true)
    );
}

fn check_error_or<F: FnOnce() -> R + std::panic::UnwindSafe, R>(f: F, str: &str, or_str: &str) {
    assert_eq!(
        std::panic::catch_unwind(f).err().and_then(|a| a
            .downcast_ref::<String>()
            .map(|s| { s.contains(str) || s.contains(or_str) })),
        Some(true)
    );
}
