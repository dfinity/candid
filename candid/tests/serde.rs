use candid::{CandidType, Decode, Deserialize, Encode, Int, Nat};

#[test]
fn test_error() {
    check_error(
        || test_decode(b"DID", &42),
        "wrong magic number [68, 73, 68, 0]",
    );
    check_error(
        || test_decode(b"DIDL", &42),
        "leb128::read::Error: failed to fill whole buffer",
    );
    check_error(
        || test_decode(b"DIDL\0\0", &42),
        "No more values to deserialize",
    );
    check_error(
        || test_decode(b"DIDL\x01\x7c", &42),
        "Unsupported op_code -4 in type table",
    );
    // Infinite loop are prevented by design
    check_error(
        || test_decode(b"DIDL\x02\x6e\x01\0", &42),
        "Unsupported op_code 0 in type table",
    );
    check_error(
        || test_decode(b"DIDL\0\x01\x7e\x01\x01", &true),
        "Trailing value after finishing deserialization",
    );
    check_error(
        || test_decode(b"DIDL\0\x01\x7e", &true),
        "io error: failed to fill whole buffer",
    );
    // Out of bounds type index
    check_error(|| test_decode(b"DIDL\0\x01\0\x01", &42), "Unknown opcode 0");
}

#[test]
fn test_bool() {
    all_check(true, "4449444c00017e01");
    all_check(false, "4449444c00017e00");
}

#[test]
fn test_integer() {
    all_check(Int::from(42), "4449444c00017c2a");
    all_check(Nat::from(42), "4449444c00017d2a");
    all_check(Int::from(1_234_567_890), "4449444c00017cd285d8cc04");
    all_check(Nat::from(1_234_567_890), "4449444c00017dd285d8cc04");
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
    all_check(
        Int::parse(b"-60000000000000000").unwrap(),
        "4449444c00017c8080e88b96cab5957f",
    );
    check_error(
        || test_decode(&hex("4449444c00017c2a"), &42i64),
        "Type mismatch. Type on the wire: Int; Provided type: Int64",
    );
}

#[test]
fn test_fixed_number() {
    all_check(42u8, "4449444c00017b2a");
    all_check(42u16, "4449444c00017a2a00");
    all_check(42u32, "4449444c0001792a000000");
    all_check(42u64, "4449444c0001782a00000000000000");
    all_check(42usize, "4449444c0001782a00000000000000");
    all_check(42i8, "4449444c0001772a");
    all_check(42i16, "4449444c0001762a00");
    all_check(42i32, "4449444c0001752a000000");
    all_check(42i64, "4449444c0001742a00000000000000");
    all_check(-42i64, "4449444c000174d6ffffffffffffff");
    all_check(-42isize, "4449444c000174d6ffffffffffffff");
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
}

#[test]
fn test_reserved() {
    use candid::{Empty, Reserved};
    all_check(Reserved, "4449444c000170");
    let res: Result<u8, Empty> = Ok(1);
    all_check(res, "4449444c016b02bc8a017bc5fed2016f01000001");
    let bytes = hex("4449444c016b02bc8a017bc5fed2016f010001");
    check_error(
        || Decode!(&bytes, Result<u8, Empty>).unwrap(),
        "Cannot decode empty type",
    );
}

#[test]
fn test_principal() {
    use candid::Principal;
    all_check(
        Principal::from_text("ic:caffee59").unwrap(),
        "4449444c0001680103caffee",
    );
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
}

#[test]
fn test_newtype() {
    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    struct X(i32);
    all_check(X(42), "4449444c016c01007501002a000000");
    
    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    enum Y {
        A(i32)
    }
    all_check(Y::A(42), "4449444c026b0141016c0100750100002a000000");
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
        "missing field `bar`",
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
    // without memoization on the unrolled type, type table will have 3 entries.
    all_check(list, "4449444c026e016c02a0d2aca8047c90eddae70400010000");
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
    check_error(|| test_decode(&bytes, &a2), "missing field `baz`");

    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    enum E2 {
        Foo,
        Bar(A1, A2),
        Baz,
    }
    // E1, E2 can be used interchangably as long as the variant matches
    let bytes = encode(&E1::Foo);
    test_decode(&bytes, &E2::Foo);
    let bytes = encode(&E2::Foo);
    test_decode(&bytes, &E1::Foo);
    let bytes = encode(&E2::Baz);
    check_error(
        || test_decode(&bytes, &E1::Bar),
        "Unknown variant hash 3303867",
    );
}

#[test]
fn test_mutual_recursion() {
    type List = Option<ListA>;
    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    struct ListA {
        head: Int,
        tail: Box<List>,
    };

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
}

#[test]
fn test_tuple() {
    all_check(
        (Int::from(42), "💩".to_string()),
        "4449444c016c02007c017101002a04f09f92a9",
    );
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
        "Expect vector index 1, but get 2",
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
        "variant index 3 larger than length 2",
    );

    check_error(
        || test_decode(&hex("4449444c016b02b4d3c9017fe6fdd5017f010000"), &Unit::Bar),
        "Unknown variant hash 3303860",
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
}

#[test]
fn test_generics() {
    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    struct G<T, E> {
        g1: T,
        g2: E,
    }

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

    check_error(
        || test_decode(&bytes, &Int::from(42)),
        "3 more values need to be deserialized",
    );

    let bytes = Encode!(&[(Int::from(42), "text")], &(Int::from(42), "text")).unwrap();
    assert_eq!(
        bytes,
        hex("4449444c026d016c02007c0171020001012a04746578742a0474657874")
    );

    let tuple = Decode!(&bytes, Vec<(Int, &str)>, (Int, String)).unwrap();
    assert_eq!(tuple.0, [(42.into(), "text")]);
    assert_eq!(tuple.1, (42.into(), "text".to_string()));

    let err = || {
        Decode!(&bytes, Vec<(Int, &str)>, (Int, String), i32).unwrap();
        true
    };
    check_error(err, "No more values to deserialize");
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
        "\nActual\n{:02x?}\nExpected\n{:02x?}\n",
        encoded, expected
    );
}

fn test_decode<'de, T>(bytes: &'de [u8], expected: &T)
where
    T: PartialEq + serde::de::Deserialize<'de> + std::fmt::Debug,
{
    let decoded = Decode!(bytes, T).unwrap();
    assert_eq!(decoded, *expected);
}

fn encode<T: CandidType>(value: &T) -> Vec<u8> {
    Encode!(&value).unwrap()
}

fn check_error<F: FnOnce() -> R + std::panic::UnwindSafe, R>(f: F, str: &str) {
    assert_eq!(
        std::panic::catch_unwind(f)
            .err()
            .and_then(|a| a.downcast_ref::<String>().map(|s| { s.contains(str) })),
        Some(true)
    );
}
