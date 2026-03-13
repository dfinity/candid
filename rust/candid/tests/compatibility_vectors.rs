use candid::{Decode, Encode};

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
