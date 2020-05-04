extern crate candid_info;
extern crate serde_candid;

use serde_candid::{CandidType, Decode, Deserialize, Encode};

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
    all_check(42, "4449444c00017c2a");
    all_check(1_234_567_890, "4449444c00017cd285d8cc04");
    all_check(-1_234_567_890, "4449444c00017caefaa7b37b");
    all_check(Box::new(42), "4449444c00017c2a");
    check_error(
        || test_decode(&hex("4449444c00017c2a"), &42u32),
        "Type mismatch. Type on the wire: Int; Provided type: Nat",
    );
}

#[test]
fn test_text() {
    all_check("Hi ☃\n".to_string(), "4449444c00017107486920e298830a");
    let bytes = hex("4449444c00017107486920e298830a");
    test_encode(&"Hi ☃\n", &bytes);
    test_decode(&bytes, &"Hi ☃\n");
}

#[test]
fn test_option() {
    all_check(Some(42), "4449444c016e7c0100012a");
    all_check(Some(Some(42)), "4449444c026e016e7c010001012a");
    // Deserialize None of type Option<i32> to Option<String>
    let none_i32: Option<i32> = None;
    let none_str: Option<String> = None;
    let bytes = Encode!(&none_i32);
    test_decode(&bytes, &none_str);
    all_check(none_i32, "4449444c016e7c010000");
    // Deserialize \mu T.Option<T> to a non-recursive type
    let v: Option<Option<Option<i32>>> = Some(Some(None));
    test_decode(b"DIDL\x01\x6e\0\x01\0\x01\x01\0", &v);
}

#[test]
fn test_struct() {
    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    struct A1 {
        foo: i32,
        bar: bool,
    }
    let a1 = A1 { foo: 42, bar: true };
    all_check(a1, "4449444c016c02d3e3aa027e868eb7027c0100012a");

    // Field name hash is larger than u32
    check_error(
        || {
            test_decode(
                &hex("4449444c016c02a3e0d4b9bf86027e868eb7027c0100012a"),
                &A1 { foo: 42, bar: true },
            )
        },
        "missing field `bar`",
    );

    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    struct A11 {
        foo: i32,
        bar: bool,
        baz: A1,
    }
    all_check(
        A11 {
            foo: 42,
            bar: true,
            baz: A1 {
                foo: 10,
                bar: false,
            },
        },
        "4449444c026c03d3e3aa027edbe3aa0201868eb7027c6c02d3e3aa027e868eb7027c010001000a2a",
    );

    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    struct B(bool, i32);
    all_check(B(true, 42), "4449444c016c02007e017c0100012a");

    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    struct List {
        head: i32,
        tail: Option<Box<List>>,
    }

    let list = List {
        head: 42,
        tail: Some(Box::new(List {
            head: 43,
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
    let bytes = Encode!(&a2);
    test_decode(&bytes, &a1);
    // Cannot Decode A1 to A2
    let bytes = Encode!(&a1);
    check_error(|| test_decode(&bytes, &a2), "missing field `baz`");

    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    enum E2 {
        Foo,
        Bar(A1, A2),
        Baz,
    }
    // E1, E2 can be used interchangably as long as the variant matches
    let bytes = Encode!(&E1::Foo);
    test_decode(&bytes, &E2::Foo);
    let bytes = Encode!(&E2::Foo);
    test_decode(&bytes, &E1::Foo);
    let bytes = Encode!(&E2::Baz);
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
        head: i32,
        tail: Box<List>,
    };

    let list: List = None;
    all_check(list, "4449444c026e016c02a0d2aca8047c90eddae70400010000");
}

#[test]
fn test_vector() {
    all_check(vec![0, 1, 2, 3], "4449444c016d7c01000400010203");
    all_check([0, 1, 2, 3], "4449444c016d7c01000400010203");
    let boxed_array: Box<[i32]> = Box::new([0, 1, 2, 3]);
    all_check(boxed_array, "4449444c016d7c01000400010203");
    all_check(
        [(42, "text".to_string())],
        "4449444c026d016c02007c01710100012a0474657874",
    );
    all_check([[[[()]]]], "4449444c046d016d026d036d7f010001010101");
    // Space bomb!
    all_check(vec![(); 1000], "4449444c016d7f0100e807");
}

#[test]
fn test_tuple() {
    all_check(
        (42, "💩".to_string()),
        "4449444c016c02007c017101002a04f09f92a9",
    );
    let none: Option<String> = None;
    let bytes =
        hex("4449444c046c04007c017e020103026d7c6e036c02a0d2aca8047c90eddae7040201002b010302030400");
    test_decode(&bytes, &(43, true, [2, 3, 4], none));
    check_error(
        || test_decode(&hex("4449444c016c02007c027101002a04f09f92a9"), &(42, "💩")),
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
        Bar(bool, i32),
        Baz { a: i32, b: u32 },
    }

    let v = E::Bar(true, 42);
    all_check(
        v,
        "4449444c036b03b3d3c90101bbd3c90102e6fdd5017f6c02007e017c6c02617c627d010000012a",
    );
}

#[test]
fn test_generics() {
    #[derive(PartialEq, Debug, Deserialize, CandidType)]
    struct G<T, E> {
        g1: T,
        g2: E,
    }

    let res = G { g1: 42, g2: true };
    all_check(res, "4449444c016c02eab3017cebb3017e01002a01")
}

#[test]
fn test_multiargs() {
    let bytes = Encode!();
    assert_eq!(bytes, b"DIDL\0\0");
    Decode!(&bytes,);

    let bytes = Encode!(&42, &Some(42), &Some(1), &Some(2));
    assert_eq!(bytes, hex("4449444c016e7c047c0000002a012a01010102"));

    Decode!(
        &bytes,
        a: i32,
        b: Option<i32>,
        c: Option<i32>,
        d: Option<i32>
    );
    assert_eq!(a, 42);
    assert_eq!(b, Some(42));
    assert_eq!(c, Some(1));
    assert_eq!(d, Some(2));

    check_error(
        || test_decode(&bytes, &42),
        "3 more values need to be deserialized",
    );

    let bytes = Encode!(&[(42, "text")], &(42, "text"));
    assert_eq!(
        bytes,
        hex("4449444c026d016c02007c0171020001012a04746578742a0474657874")
    );

    Decode!(&bytes, a: Vec<(i64, &str)>, b: (i64, String));
    assert_eq!(a, [(42, "text")]);
    assert_eq!(b, (42, "text".to_string()));

    let err = || {
        Decode!(&bytes, _a: Vec<(i64, &str)>, _b: (i64, String), _c: i32);
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
    let encoded = Encode!(&value);
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
    Decode!(bytes, decoded: T);
    assert_eq!(decoded, *expected);
}

fn check_error<F: FnOnce() -> R + std::panic::UnwindSafe, R>(f: F, str: &str) {
    assert_eq!(
        std::panic::catch_unwind(f)
            .err()
            .and_then(|a| a.downcast_ref::<String>().map(|s| { s.contains(str) })),
        Some(true)
    );
}
