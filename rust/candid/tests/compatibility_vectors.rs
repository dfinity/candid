use candid::{CandidType, Decode, Deserialize, Encode};

#[test]
fn primitive_vector_decode_stays_compatible_with_extra_args() {
    let values = vec![-1i16, 0, 1, 42, i16::MIN, i16::MAX];
    let bytes = Encode!(&values, &123u8).unwrap();

    let decoded_values = Decode!(&bytes, Vec<i16>).unwrap();
    assert_eq!(decoded_values, values);

    let (decoded_values, trailing) = Decode!(&bytes, Vec<i16>, u8).unwrap();
    assert_eq!(decoded_values, values);
    assert_eq!(trailing, 123);
}

#[test]
fn nested_primitive_vector_decode() {
    // Outer vec is non-primitive so exact_primitive is None; inner vecs use the fast path.
    let values: Vec<Vec<i16>> = vec![vec![1, 2], vec![], vec![3, i16::MIN, i16::MAX]];
    let bytes = Encode!(&values).unwrap();
    let decoded: Vec<Vec<i16>> = Decode!(&bytes, Vec<Vec<i16>>).unwrap();
    assert_eq!(decoded, values);
}

#[test]
fn struct_with_primitive_vector_field() {
    // Ensures primitive_vec_fast_path is correctly restored when a vec<primitive>
    // appears as a struct field alongside other fields.
    #[derive(CandidType, Deserialize, PartialEq, Debug)]
    struct S {
        xs: Vec<i32>,
        y: u8,
    }
    let s = S {
        xs: vec![1, -1, i32::MAX],
        y: 42,
    };
    let bytes = Encode!(&s).unwrap();
    let decoded = Decode!(&bytes, S).unwrap();
    assert_eq!(decoded, s);
}

#[test]
fn mismatched_rust_type_does_not_use_fast_path() {
    // Wire type is vec nat16 but Rust target is Vec<u32>: expect and wire differ,
    // so exact_primitive is None and the normal type-checking path rejects it.
    let values: Vec<u16> = vec![1, 2, 3];
    let bytes = Encode!(&values).unwrap();
    assert!(Decode!(&bytes, Vec<u32>).is_err());
}

#[test]
fn bulk_encode_primitive_vectors_round_trip() {
    let u8s: Vec<u8> = vec![0, 1, 127, 255];
    assert_eq!(Decode!(&Encode!(&u8s).unwrap(), Vec<u8>).unwrap(), u8s);

    let i16s: Vec<i16> = vec![i16::MIN, -1, 0, 1, i16::MAX];
    assert_eq!(Decode!(&Encode!(&i16s).unwrap(), Vec<i16>).unwrap(), i16s);

    let u32s: Vec<u32> = vec![0, 1, u32::MAX];
    assert_eq!(Decode!(&Encode!(&u32s).unwrap(), Vec<u32>).unwrap(), u32s);

    let f64s: Vec<f64> = vec![0.0, -1.0, f64::INFINITY, f64::NAN];
    let decoded = Decode!(&Encode!(&f64s).unwrap(), Vec<f64>).unwrap();
    assert_eq!(decoded[0], 0.0);
    assert_eq!(decoded[1], -1.0);
    assert_eq!(decoded[2], f64::INFINITY);
    assert!(decoded[3].is_nan());

    let bools: Vec<bool> = vec![true, false, true];
    assert_eq!(
        Decode!(&Encode!(&bools).unwrap(), Vec<bool>).unwrap(),
        bools
    );

    let empty: Vec<i32> = vec![];
    assert_eq!(Decode!(&Encode!(&empty).unwrap(), Vec<i32>).unwrap(), empty);
}

#[test]
fn primitive_vector_is_extra_args() {
    let extra = vec![1i16, 2, 3];
    let bytes = Encode!(&123u8, &extra).unwrap();

    let decoded_values = Decode!(&bytes, u8).unwrap();
    assert_eq!(decoded_values, 123);
}
