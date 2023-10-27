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
pub fn decode_nat<R>(r: &mut R) -> Result<u128>
where
    R: io::Read + ?Sized,
{
    let mut result = 0;
    let mut shift = 0;
    loop {
        let mut buf = [0];
        r.read_exact(&mut buf)?;
        if shift == 127 && buf[0] != 0x00 && buf[0] != 0x01 {
            while buf[0] & CONTINUATION_BIT != 0 {
                r.read_exact(&mut buf)?;
            }
            return Err(Error::msg("nat overflow"));
        }
        let low_bits = (buf[0] & !CONTINUATION_BIT) as u128;
        result |= low_bits << shift;
        if buf[0] & CONTINUATION_BIT == 0 {
            return Ok(result);
        }
        shift += 7;
    }
}
pub fn decode_int<R>(r: &mut R) -> Result<i128>
where
    R: io::Read + ?Sized,
{
    let mut result = 0;
    let mut shift = 0;
    let size = 128;
    let mut byte;
    loop {
        let mut buf = [0];
        r.read_exact(&mut buf)?;
        byte = buf[0];
        if shift == 127 && byte != 0x00 && byte != 0x7f {
            while buf[0] & CONTINUATION_BIT != 0 {
                r.read_exact(&mut buf)?;
            }
            return Err(Error::msg("int overflow"));
        }
        let low_bits = (byte & !CONTINUATION_BIT) as i128;
        result |= low_bits << shift;
        shift += 7;
        if byte & CONTINUATION_BIT == 0 {
            break;
        }
    }
    if shift < size && (byte & SIGN_BIT) == SIGN_BIT {
        result |= !0 << shift;
    }
    Ok(result)
}
