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

/// A `len`-byte LEB128 body (`len >= 1`) whose 7-bit groups are all `0x7f`:
/// `len - 1` continuation bytes (`0xff`) followed by a terminator (`0x7f`).
/// Decoded as a `nat` this is `2^(7*len) - 1`; decoded as an `int` (sign bit set
/// on the final group) it is `-1`. Handy for exercising the bignum path with a
/// long value.
fn all_ones_leb128(len: usize) -> Vec<u8> {
    let mut bytes = vec![0xffu8; len - 1];
    bytes.push(0x7f);
    bytes
}

/// Values straddling the `u64` fast-path boundary must all roundtrip, including
/// the first one that overflows it and so takes the bignum path.
#[test]
fn nat_u64_boundary_roundtrip() {
    for v in [
        0u128,
        u128::from(u64::MAX) - 1,
        u128::from(u64::MAX),
        u128::from(u64::MAX) + 1,
        u128::MAX,
    ] {
        let n = Nat::from(v);
        let mut enc = Vec::new();
        n.encode(&mut enc).unwrap();
        let decoded = Nat::decode(&mut &enc[..]).unwrap();
        assert_eq!(decoded, n, "nat boundary value {v}");
    }
}

/// Values straddling the positive and negative `i64` fast-path boundaries.
#[test]
fn int_i64_boundary_roundtrip() {
    for v in [
        0i128,
        i128::from(i64::MAX),
        i128::from(i64::MAX) + 1,
        i128::from(i64::MIN),
        i128::from(i64::MIN) - 1,
        i128::MAX,
        i128::MIN,
    ] {
        let i = Int::from(v);
        let mut enc = Vec::new();
        i.encode(&mut enc).unwrap();
        let decoded = Int::decode(&mut &enc[..]).unwrap();
        assert_eq!(decoded, i, "int boundary value {v}");
    }
}

/// Large `nat` values exercise the bignum decode path at scale. `2^(7*len) - 1`
/// is its own canonical LEB128 encoding (all groups are `0x7f`), so re-encoding
/// the decoded value must reproduce the input byte-for-byte.
#[test]
fn nat_large_bignum_roundtrip() {
    for len in [10usize, 11, 100, 1000, 50_000] {
        let bytes = all_ones_leb128(len);
        let n = Nat::decode(&mut &bytes[..]).unwrap();
        let mut re = Vec::new();
        n.encode(&mut re).unwrap();
        assert_eq!(re, bytes, "nat len={len} canonical re-encode");
        // Confirm the value really overflowed the u64 fast path.
        assert!(n.0.to_u64().is_none(), "nat len={len} must exceed u64");
    }
}

/// An all-`0xff`..`0x7f` sleb128 stream decodes to `-1` regardless of length:
/// the sign bit is set and every magnitude bit is one. Exercises the bignum
/// path's two's-complement sign handling for arbitrarily long inputs.
#[test]
fn int_all_continuation_is_minus_one() {
    for len in [2usize, 10, 100, 1000, 50_000] {
        let bytes = all_ones_leb128(len);
        let i = Int::decode(&mut &bytes[..]).unwrap();
        assert_eq!(
            i,
            Int::from(-1),
            "all-0xff sleb128 (len={len}) decodes to -1"
        );
    }
}

/// `len - 1` zero groups (`0x80`) then a `0x7f` terminator decodes to
/// `-2^(7*(len-1))`: a genuine large-magnitude negative bignum. Re-encoding and
/// decoding must be stable.
#[test]
fn int_large_negative_bignum_roundtrip() {
    let zero = Int::from(0);
    for len in [11usize, 100, 1000, 50_000] {
        let mut bytes = vec![0x80u8; len - 1];
        bytes.push(0x7f);
        let i = Int::decode(&mut &bytes[..]).unwrap();
        assert!(i < zero, "len={len} should be negative");
        let mut re = Vec::new();
        i.encode(&mut re).unwrap();
        let i2 = Int::decode(&mut &re[..]).unwrap();
        assert_eq!(i, i2, "neg bignum roundtrip len={len}");
    }
}

/// Randomized roundtrip over large (beyond u64/i64) `nat`/`int` values, covering
/// both signs. `decode` is independently pinned by the exact-byte and
/// closed-form tests above, so `decode(encode(v)) == v` validates that `encode`
/// is semantically correct, and byte-stability under re-encode confirms the
/// output is canonical (minimal).
#[test]
fn bignum_random_roundtrip() {
    use rand::Rng;
    let mut rng = rand::thread_rng();

    let roundtrip_nat = |n: &Nat| {
        let mut enc = Vec::new();
        n.encode(&mut enc).unwrap();
        let dec = Nat::decode(&mut &enc[..]).unwrap();
        assert_eq!(&dec, n, "nat decode(encode(v)) == v");
        let mut enc2 = Vec::new();
        dec.encode(&mut enc2).unwrap();
        assert_eq!(enc, enc2, "nat canonical re-encode");
    };
    let roundtrip_int = |i: &Int| {
        let mut enc = Vec::new();
        i.encode(&mut enc).unwrap();
        let dec = Int::decode(&mut &enc[..]).unwrap();
        assert_eq!(&dec, i, "int decode(encode(v)) == v");
        let mut enc2 = Vec::new();
        dec.encode(&mut enc2).unwrap();
        assert_eq!(enc, enc2, "int canonical re-encode");
    };

    for _ in 0..1000 {
        // Grow well past u64/i64 (>= 2^150) so the bignum path is exercised.
        let mut nat = Nat::from(rng.gen::<u64>());
        let mut int = Int::from(rng.gen::<i64>());
        for _ in 0..rng.gen_range(4..12) {
            nat = nat * (1u64 << 50) + rng.gen::<u64>();
            int = int * (1i64 << 50) + rng.gen::<i64>();
        }
        roundtrip_nat(&nat);
        roundtrip_int(&int);
        roundtrip_int(&(int * (-1i128))); // exercise the negative encode path too
    }
}
