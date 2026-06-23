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
        Int::from(0),
        Int::from(-1),
        Int::from(42),
        Int::from(i64::MIN),
        Int::from(i64::MAX),
        Int::parse(b"24197857200151251861972493965091130863").unwrap(),
        Int::parse(b"-600000000000000000000000000000000000").unwrap(),
    ];
    let int_bytes = Encode!(&int_values).unwrap();
    let decoded_int_values = Decode!(&int_bytes, Vec<Int>).unwrap();
    assert_eq!(decoded_int_values, int_values);
}

/// Test the exact fast-path/BigInt transition boundaries using raw encode/decode.
#[test]
fn nat_decode_fast_path_boundaries() {
    fn roundtrip(n: Nat) -> Nat {
        let mut buf = Vec::new();
        n.encode(&mut buf).unwrap();
        Nat::decode(&mut buf.as_slice()).unwrap()
    }

    // Last value handled entirely by the u64 fast path.
    assert_eq!(roundtrip(Nat::from(u64::MAX)), Nat::from(u64::MAX));

    // First value that overflows u64: must fall back to BigInt.
    // u64::MAX + 1 = 18446744073709551616
    let just_over = Nat::parse(b"18446744073709551616").unwrap();
    assert_eq!(roundtrip(just_over.clone()), just_over);

    // A few values straddling the boundary.
    for delta in 0u64..=8 {
        let base = Nat::from(u64::MAX) - Nat::from(delta);
        assert_eq!(roundtrip(base.clone()), base);
    }
}

/// Test the exact fast-path/BigInt transition boundaries for signed LEB128.
#[test]
fn int_decode_fast_path_boundaries() {
    fn roundtrip(n: Int) -> Int {
        let mut buf = Vec::new();
        n.encode(&mut buf).unwrap();
        Int::decode(&mut buf.as_slice()).unwrap()
    }

    // Largest positive i64: handled by fast path.
    assert_eq!(roundtrip(Int::from(i64::MAX)), Int::from(i64::MAX));

    // 2^63 = i64::MAX + 1: fits u64 but not i64 (positive BigInt branch).
    let just_over_pos = Int::parse(b"9223372036854775808").unwrap();
    assert_eq!(roundtrip(just_over_pos.clone()), just_over_pos);

    // Most negative i64: fast path with sign extension.
    assert_eq!(roundtrip(Int::from(i64::MIN)), Int::from(i64::MIN));

    // i64::MIN - 1: must fall back to BigInt negative path.
    let just_under_neg = Int::parse(b"-9223372036854775809").unwrap();
    assert_eq!(roundtrip(just_under_neg.clone()), just_under_neg);
}
