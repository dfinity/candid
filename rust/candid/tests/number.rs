use candid::types::leb128::*;
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
fn pretty_print_numbers() {
    assert_eq!(format!("{}", Nat::from(42u8)), "42");
    assert_eq!(format!("{}", Nat::from(100u8)), "100");
    assert_eq!(format!("{}", Nat::from(100000u32)), "100_000");
    assert_eq!(format!("{}", Nat::from(1_234_567_890u32)), "1_234_567_890");
    assert_eq!(format!("{}", Int::from(0)), "0");
    assert_eq!(format!("{}", Int::from(-1)), "-1");
    assert_eq!(format!("{}", Int::from(-123)), "-123");
    assert_eq!(format!("{}", Int::from(-12345678)), "-12_345_678");
    assert_eq!(format!("{}", Int::from(12345678)), "12_345_678");
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
            encoded.clear();
            encode_int(&mut encoded, x.into()).unwrap();
            assert_eq!(expected, encoded);
        }
        let mut readable = &expected[..];
        let decoded = Int::decode(&mut readable).unwrap();
        assert_eq!(decoded.0.to_i64().unwrap(), x);
        readable = &expected[..];
        let decoded = decode_int(&mut readable).unwrap();
        assert_eq!(decoded as i64, x);
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
            encoded.clear();
            encode_nat(&mut encoded, x.into()).unwrap();
            assert_eq!(expected, encoded);
        }
        let mut readable = &expected[..];
        let decoded = Nat::decode(&mut readable).unwrap();
        assert_eq!(decoded.0.to_u64().unwrap(), x);
        readable = &expected[..];
        let decoded = decode_nat(&mut readable).unwrap();
        assert_eq!(decoded as u64, x);
    }
}

#[allow(clippy::cmp_owned)]
#[test]
fn operators() {
    macro_rules! test_type_nat {
        ($( $t: ty )*) => ($(
            let x: $t = 1;
            let value = <Nat>::from(x + 1);

            assert_eq!(value.clone() + x, 3u32);
            assert_eq!(value.clone() - x, 1u32);
            assert_eq!(value.clone() * x, 2u32);
            assert_eq!(value.clone() / x, 2u32);
            assert_eq!(value.clone() % x, 0u32);

            assert_eq!(x + value.clone(), 3u32);
            let result = std::panic::catch_unwind(|| x - value.clone());
            assert!(result.is_err());
            assert_eq!(x * value.clone(), 2u32);
            assert_eq!(x / value.clone(), 0u32);
            assert_eq!(x % value.clone(), 1u32);

            assert!(value.clone() < <Nat>::from(x + 2));
            assert!(<Nat>::from(x + 2) > value.clone());
            assert!(x < <Nat>::from(x + 2));
            assert!(<Nat>::from(x + 2) > x);
        )*)
    }
    macro_rules! test_type_int {
        ($( $t: ty )*) => ($(
            let x: $t = 1;
            let value = <Int>::from(x + 1);

            assert_eq!(value.clone() + x, 3);
            assert_eq!(value.clone() - x, 1);
            assert_eq!(value.clone() * x, 2);
            assert_eq!(value.clone() / x, 2);
            assert_eq!(value.clone() % x, 0);

            assert_eq!(x + value.clone(), 3);
            assert_eq!(x - value.clone(), -1);
            assert_eq!(x * value.clone(), 2);
            assert_eq!(x / value.clone(), 0);
            assert_eq!(x % value.clone(), 1);

            assert!(value.clone() < <Int>::from(x + 2));
            assert!(<Int>::from(x + 2) > value.clone());
            assert!(x < <Int>::from(x + 2));
            assert!(<Int>::from(x + 2) > x);
        )*)
    }

    test_type_nat!( usize u8 u16 u32 u64 u128 );
    test_type_int!( usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128 );
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
    if !nat_hex.is_empty() {
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
