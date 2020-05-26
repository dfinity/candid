use candid::{Int, Nat};
use num_bigint::{BigInt, BigUint};

#[test]
fn test_numbers() {
    check(b"0", "00", "00");
    check(b"127", "ff00", "7f");
    check(b"-1", "7f", "");
    check(b"-123456", "c0bb78", "");
    check(b"624485", "e58e26", "e58e26");
    check(b"2000000", "8089fa00", "80897a");
    check(
        b"60000000000000000",
        "808098f4e9b5caea00",
        "808098f4e9b5ca6a",
    );
    check(
        b"24197857200151252728969465429440056815",
        "ef9baf8589cf959a92deb7de8a929eabb424",
        "ef9baf8589cf959a92deb7de8a929eabb424",
    );
    check(
        b"-24197857200151252728969465429440056815",
        "91e4d0faf6b0eae5eda1c8a1f5ede1d4cb5b",
        "",
    );
}

fn check(num: &[u8], int_hex: &str, nat_hex: &str) {
    use std::io::Cursor;
    let v = Int(BigInt::parse_bytes(num, 10).unwrap());
    let bytes = hex::decode(int_hex).unwrap();
    // Check encode
    let mut encoded = Vec::new();
    v.encode(&mut encoded).unwrap();
    assert_eq!(encoded, bytes);
    // Check decode
    let mut rcr = Cursor::new(encoded);
    let decoded = Int::decode(&mut rcr).unwrap();
    assert_eq!(decoded, v);
    // Check for Nat
    if nat_hex != "" {
        let nat = Nat(BigUint::parse_bytes(num, 10).unwrap());
        let bytes = hex::decode(nat_hex).unwrap();
        // Check encode
        let mut encoded = Vec::new();
        nat.encode(&mut encoded).unwrap();
        assert_eq!(encoded, bytes);
        // Check decode
        let mut rcr = Cursor::new(encoded);
        let decoded = Nat::decode(&mut rcr).unwrap();
        assert_eq!(decoded, nat);
    }
}
