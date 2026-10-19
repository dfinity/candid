use crate::error::{Error, Result};
use std::io;

// Code copied from https://github.com/gimli-rs/leb128/blob/master/src/lib.rs.
// Changing the type from i64 to i128

const CONTINUATION_BIT: u8 = 1 << 7;
const SIGN_BIT: u8 = 1 << 6;

pub fn encode_nat<W>(w: &mut W, mut val: u128) -> Result<()>
where
    W: io::Write + ?Sized,
{
    loop {
        let mut byte = (val & 0x7fu128) as u8;
        val >>= 7;
        if val != 0 {
            byte |= CONTINUATION_BIT;
        }
        let buf = [byte];
        w.write_all(&buf)?;
        if val == 0 {
            return Ok(());
        }
    }
}
pub fn encode_int<W>(w: &mut W, mut val: i128) -> Result<()>
where
    W: io::Write + ?Sized,
{
    loop {
        let mut byte = val as u8;
        val >>= 6;
        let done = val == 0 || val == -1;
        if done {
            byte &= !CONTINUATION_BIT;
        } else {
            val >>= 1;
            byte |= CONTINUATION_BIT;
        }
        let buf = [byte];
        w.write_all(&buf)?;
        if done {
            return Ok(());
        }
    }
}
/// Decodes an unsigned LEB128 value into a `u128`.
///
/// The whole LEB128 body is always consumed. Groups that lie past bit 127 are
/// accepted as long as they are zero (an overlong encoding of a value that fits),
/// matching what [`crate::Nat::decode`] reads from the same bytes. Any set bit at
/// position 128 or above yields a "nat overflow" error.
pub fn decode_nat<R>(r: &mut R) -> Result<u128>
where
    R: io::Read + ?Sized,
{
    let mut result: u128 = 0;
    let mut shift: u32 = 0;
    let mut overflow = false;
    loop {
        let mut buf = [0];
        r.read_exact(&mut buf)?;
        let byte = buf[0];
        let low_bits = (byte & !CONTINUATION_BIT) as u128;
        if shift < 128 {
            // Bits of this group that land at position 128 or above.
            if shift > 121 && low_bits >> (128 - shift) != 0 {
                overflow = true;
            }
            result |= low_bits << shift;
        } else if low_bits != 0 {
            overflow = true;
        }
        if byte & CONTINUATION_BIT == 0 {
            break;
        }
        shift = shift.saturating_add(7);
    }
    if overflow {
        return Err(Error::msg("nat overflow"));
    }
    Ok(result)
}
/// Decodes a signed LEB128 value into an `i128`.
///
/// The whole LEB128 body is always consumed. Groups that lie past bit 127 are
/// accepted as long as they only sign-extend the value (an overlong encoding of a
/// value that fits), matching what [`crate::Int::decode`] reads from the same
/// bytes. Otherwise the result is an "int overflow" error.
pub fn decode_int<R>(r: &mut R) -> Result<i128>
where
    R: io::Read + ?Sized,
{
    let mut result: i128 = 0;
    let mut shift: u32 = 0;
    // Bits at position 127 and above must all equal the sign of the value, so
    // they must be all zeros or all ones.
    let mut high_zero = true;
    let mut high_one = true;
    let mut byte;
    loop {
        let mut buf = [0];
        r.read_exact(&mut buf)?;
        byte = buf[0];
        let low_bits = byte & !CONTINUATION_BIT;
        if shift < 128 {
            if shift > 120 {
                // Bits of this group from position 127 up.
                let high = low_bits >> (127 - shift);
                let mask = 0x7f >> (127 - shift);
                high_zero &= high == 0;
                high_one &= high == mask;
            }
            result |= (low_bits as i128) << shift;
        } else {
            high_zero &= low_bits == 0;
            high_one &= low_bits == 0x7f;
        }
        shift = shift.saturating_add(7);
        if byte & CONTINUATION_BIT == 0 {
            break;
        }
    }
    if !high_zero && !high_one {
        return Err(Error::msg("int overflow"));
    }
    if shift < 128 && (byte & SIGN_BIT) == SIGN_BIT {
        result |= !0 << shift;
    }
    Ok(result)
}
