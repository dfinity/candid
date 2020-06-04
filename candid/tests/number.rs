use candid::{Int, Nat};
use num_traits::cast::ToPrimitive;

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

#[test]
fn random_i64() {
    use rand::Rng;
    let mut rng = rand::thread_rng();
    for _ in 0..10000 {
        let x: i64 = rng.gen();
        let mut expected = Vec::new();
        leb128::write::signed(&mut expected, x).unwrap();
        {
            let mut encoded = Vec::new();
            Int::from(x).encode(&mut encoded).unwrap();
            assert_eq!(expected, encoded);
        }
        let mut readable = &expected[..];
        let decoded = Int::decode(&mut readable).unwrap();
        assert_eq!(decoded.0.to_i64().unwrap(), x);
    }
}

#[test]
fn random_u64() {
    use rand::Rng;
    let mut rng = rand::thread_rng();
    for _ in 0..10000 {
        let x: u64 = rng.gen();
        let mut expected = Vec::new();
        leb128::write::unsigned(&mut expected, x).unwrap();
        {
            let mut encoded = Vec::new();
            Nat::from(x).encode(&mut encoded).unwrap();
            assert_eq!(expected, encoded);
        }
        let mut readable = &expected[..];
        let decoded = Nat::decode(&mut readable).unwrap();
        assert_eq!(decoded.0.to_u64().unwrap(), x);
    }
}

fn check(num: &str, int_hex: &str, nat_hex: &str) {
    let v = num.parse::<Int>().unwrap();
    let bytes = hex::decode(int_hex).unwrap();
    // Check encode
    let mut encoded = Vec::new();
    v.encode(&mut encoded).unwrap();
    assert_eq!(encoded, bytes);
    // Check decode
    let mut rcr = &encoded[..];
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
        let mut rcr = &encoded[..];
        let decoded = Nat::decode(&mut rcr).unwrap();
        assert_eq!(decoded, nat);
    }
}
