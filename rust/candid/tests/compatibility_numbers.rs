use candid::{Decode, Encode, Int, Nat};

#[test]
fn number_fast_paths_preserve_small_and_large_values() {
    let nat_values = vec![
        Nat::from(0u8),
        Nat::from(42u64),
        Nat::from(u64::MAX),
        Nat::parse(b"24197857200151251861972493965091130863").unwrap(),
    ];
    let nat_bytes = Encode!(&nat_values).unwrap();
    let decoded_nat_values = Decode!(&nat_bytes, Vec<Nat>).unwrap();
    assert_eq!(decoded_nat_values, nat_values);

    let int_values = vec![
        Int::from(-1),
        Int::from(42),
        Int::from(i64::MIN),
        Int::parse(b"-600000000000000000000000000000000000").unwrap(),
    ];
    let int_bytes = Encode!(&int_values).unwrap();
    let decoded_int_values = Decode!(&int_bytes, Vec<Int>).unwrap();
    assert_eq!(decoded_int_values, int_values);
}
