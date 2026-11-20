//! LEB128 and SLEB128 (`lean/Spec/Binary.md`, Section 3.1). Mirrors the LEB128 section of
//! `lean/Candid/Wire.lean`.
//!
//! A decoder must accept a number in any number of bytes, so a reader cannot stop at ten:
//! `80 80 ... 00` is 0 however long it is. What it can do is say when the number does not
//! fit in 64 bits. Every use of an unsigned number in the header rejects the same
//! messages whether it is read exactly or saturated at `u64::MAX` -- a count or a length
//! that large runs past the end of any message, an index that large dangles, and a field
//! id that large is too large anyway -- so [`read_unsigned`] saturates. A signed number is
//! told apart by which way it overflows, since the two ways mean different things.

use alloc::vec::Vec;

/// A signed number as read: its value, or which way it overflows an `i64`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Signed {
    Value(i64),
    /// Above `i64::MAX`.
    Above,
    /// Below `i64::MIN`.
    Below,
}

/// Unsigned LEB128 at the start of `bytes`: the number, saturated at `u64::MAX`, and how
/// many bytes it took. `None` if `bytes` ends before the number does.
pub(crate) fn read_unsigned(bytes: &[u8]) -> Option<(u64, usize)> {
    let mut value: u64 = 0;
    for (i, &byte) in bytes.iter().enumerate() {
        let group = u64::from(byte & 0x7f);
        let shift = i.saturating_mul(7);
        if group != 0 {
            value = match u32::try_from(shift).ok().and_then(|s| group.checked_shl(s)) {
                // `checked_shl` only refuses a shift past the width; bits shifted out
                // are lost silently, so check that none were.
                Some(bits) if bits >> shift == group => value | bits,
                _ => u64::MAX,
            };
        }
        if byte < 0x80 {
            return Some((value, i + 1));
        }
    }
    None
}

/// Signed LEB128 at the start of `bytes`: the number, or which way it overflows, and how
/// many bytes it took. `None` if `bytes` ends before the number does.
///
/// The groups below bit 63 are collected as they come. The ones from bit 63 up only have
/// to agree with the sign, which the last byte's bit 6 gives: all ones for a negative
/// number, all zeros for a non-negative one. Anything else does not fit.
pub(crate) fn read_signed(bytes: &[u8]) -> Option<(Signed, usize)> {
    let mut low: u64 = 0;
    // Whether some group from bit 63 up has a one, or a zero.
    let (mut high_one, mut high_zero) = (false, false);
    for (i, &byte) in bytes.iter().enumerate() {
        let group = u64::from(byte & 0x7f);
        // Groups 0 to 8 hold bits 0 to 62; group 9 starts at bit 63.
        let high = i >= 9;
        if high {
            high_one |= group != 0;
            high_zero |= group != 0x7f;
        } else {
            low |= group << (7 * i);
        }
        if byte < 0x80 {
            let negative = byte & 0x40 != 0;
            let signed = if !high {
                // Extend the sign from the last group's top bit, bit 7i + 6. The width
                // is at most 63, so the shift is in range.
                let width = 7 * (i + 1);
                let value = if negative {
                    low | (u64::MAX << width)
                } else {
                    low
                };
                Signed::Value(value as i64)
            } else if negative {
                if high_zero {
                    Signed::Below
                } else {
                    Signed::Value((low | 1 << 63) as i64)
                }
            } else if high_one {
                Signed::Above
            } else {
                Signed::Value(low as i64)
            };
            return Some((signed, i + 1));
        }
    }
    None
}

/// Unsigned LEB128, shortest form.
pub(crate) fn write_unsigned(out: &mut Vec<u8>, mut n: u64) {
    while n >= 0x80 {
        out.push((n & 0x7f) as u8 | 0x80);
        n >>= 7;
    }
    out.push(n as u8);
}

/// Signed LEB128, shortest form: stop once the rest is all sign, and the last byte's bit
/// 6 says which sign.
pub(crate) fn write_signed(out: &mut Vec<u8>, mut i: i64) {
    loop {
        let low = (i & 0x7f) as u8;
        i >>= 7;
        if (i == 0 && low & 0x40 == 0) || (i == -1 && low & 0x40 != 0) {
            out.push(low);
            return;
        }
        out.push(low | 0x80);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    fn unsigned(n: u64) -> Vec<u8> {
        let mut out = Vec::new();
        write_unsigned(&mut out, n);
        out
    }

    fn signed(i: i64) -> Vec<u8> {
        let mut out = Vec::new();
        write_signed(&mut out, i);
        out
    }

    /// The reading of `bytes` by a reference over `i128`, which holds 18 groups.
    fn reference_signed(bytes: &[u8]) -> Signed {
        assert!(bytes.len() <= 18);
        let mut value: i128 = 0;
        for (i, &b) in bytes.iter().enumerate() {
            value |= i128::from(b & 0x7f) << (7 * i);
        }
        let width = 7 * bytes.len() as u32;
        // Sign-extend from bit `width - 1`.
        let value = (value << (128 - width)) >> (128 - width);
        match i64::try_from(value) {
            Ok(v) => Signed::Value(v),
            Err(_) if value > 0 => Signed::Above,
            Err(_) => Signed::Below,
        }
    }

    fn reference_unsigned(bytes: &[u8]) -> u64 {
        assert!(bytes.len() <= 18);
        let mut value: u128 = 0;
        for (i, &b) in bytes.iter().enumerate() {
            value |= u128::from(b & 0x7f) << (7 * i);
        }
        u64::try_from(value).unwrap_or(u64::MAX)
    }

    #[test]
    fn spec_examples() {
        assert_eq!(unsigned(300), vec![0xac, 0x02]);
        assert_eq!(signed(-129), vec![0xff, 0x7e]);
        assert_eq!(signed(64), vec![0xc0, 0x00]);
        assert_eq!(signed(-64), vec![0x40]);
        assert_eq!(read_unsigned(&[0x80, 0x80, 0x00]), Some((0, 3)));
        assert_eq!(read_unsigned(&[0x80, 0x80]), None);
    }

    #[test]
    fn redundant_bytes_of_any_length() {
        let mut zero = vec![0x80; 100];
        zero.push(0x00);
        assert_eq!(read_unsigned(&zero), Some((0, 101)));
        assert_eq!(read_signed(&zero), Some((Signed::Value(0), 101)));

        let mut minus_one = vec![0xff; 100];
        minus_one.push(0x7f);
        assert_eq!(read_signed(&minus_one), Some((Signed::Value(-1), 101)));
    }

    #[test]
    fn overflow() {
        let mut big = vec![0x80; 10];
        big.push(0x01); // 2^70
        assert_eq!(read_unsigned(&big), Some((u64::MAX, 11)));
        assert_eq!(read_signed(&big), Some((Signed::Above, 11)));
        let mut small = vec![0x80; 10];
        small.push(0x7e); // -2^71
        assert_eq!(read_signed(&small), Some((Signed::Below, 11)));
    }

    #[test]
    fn extremes_roundtrip() {
        for n in [0, 1, 127, 128, u64::from(u32::MAX), u64::MAX - 1, u64::MAX] {
            let bytes = unsigned(n);
            assert_eq!(read_unsigned(&bytes), Some((n, bytes.len())));
        }
        for i in [0, 1, -1, 63, 64, -64, -65, i64::MAX, i64::MIN, i64::MIN + 1] {
            let bytes = signed(i);
            assert_eq!(read_signed(&bytes), Some((Signed::Value(i), bytes.len())));
        }
    }

    #[test]
    fn agrees_with_a_wider_reference() {
        // Every byte string of up to 18 bytes is too many; a deterministic sample of them,
        // weighted toward the bytes where the boundaries are.
        let interesting = [
            0x00, 0x01, 0x3f, 0x40, 0x41, 0x7e, 0x7f, 0x80, 0x81, 0xc0, 0xff,
        ];
        let mut state: u64 = 0x2545_f491_4f6c_dd1d;
        for _ in 0..200_000 {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            let len = 1 + (state % 18) as usize;
            let mut bytes: Vec<u8> = (0..len)
                .map(|k| {
                    let r = state.rotate_left(k as u32 * 5);
                    interesting[(r % interesting.len() as u64) as usize] | 0x80
                })
                .collect();
            *bytes.last_mut().unwrap() &= 0x7f;
            assert_eq!(
                read_signed(&bytes),
                Some((reference_signed(&bytes), len)),
                "{bytes:02x?}"
            );
            assert_eq!(
                read_unsigned(&bytes),
                Some((reference_unsigned(&bytes), len)),
                "{bytes:02x?}"
            );
        }
    }
}
