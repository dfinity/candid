use candid::{Int, Nat};

#[test]
fn test_numbers() {
    check("0", "00", "00");
    check("127", "ff00", "7f");
    check("-1", "7f", "");
    check("-123456", "c0bb78", "");
    check("624485", "e58e26", "e58e26");
    check("2000000", "8089fa00", "80897a");
    check(
        "60000000000000000",
        "808098f4e9b5caea00",
        "808098f4e9b5ca6a",
    );
    check(
        "24197857200151252728969465429440056815",
        "ef9baf8589cf959a92deb7de8a929eabb424",
        "ef9baf8589cf959a92deb7de8a929eabb424",
    );
    check(
        "-24197857200151252728969465429440056815",
        "91e4d0faf6b0eae5eda1c8a1f5ede1d4cb5b",
        "",
    );
}

fn check(num: &str, int_hex: &str, nat_hex: &str) {
    use std::io::Cursor;
    let v = num.parse::<Int>().unwrap();
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
        let nat = num.parse::<Nat>().unwrap();
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
