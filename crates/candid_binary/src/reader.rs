//! A reader over a message: the bytes and a position in them. Mirrors the "Reading bytes"
//! section of `lean/Candid/Wire.lean`.
//!
//! Every read either consumes at least one byte or fails, so a loop over a count read
//! from the message ends when the bytes do, however large the count. Nothing is
//! allocated in advance for a count.

use crate::error::{DecodeError, Rejection};
use crate::leb128::{self, Signed};

pub(crate) struct Reader<'a> {
    bytes: &'a [u8],
    position: usize,
}

pub(crate) type Read<T> = Result<T, DecodeError>;

impl<'a> Reader<'a> {
    pub(crate) fn new(bytes: &'a [u8]) -> Self {
        Reader { bytes, position: 0 }
    }

    pub(crate) fn position(&self) -> usize {
        self.position
    }

    /// The bytes not read yet.
    pub(crate) fn rest(&self) -> &'a [u8] {
        &self.bytes[self.position..]
    }

    /// A rejection at `position`.
    pub(crate) fn fail<T>(&self, position: usize, rejection: Rejection) -> Read<T> {
        Err(DecodeError::new(position, rejection))
    }

    pub(crate) fn byte(&mut self) -> Read<u8> {
        match self.rest().first() {
            Some(&b) => {
                self.position += 1;
                Ok(b)
            }
            None => self.fail(self.position, Rejection::EndOfInput),
        }
    }

    /// Unsigned LEB128, saturated at `u64::MAX`; see [`leb128`].
    pub(crate) fn unsigned(&mut self) -> Read<u64> {
        match leb128::read_unsigned(self.rest()) {
            Some((n, used)) => {
                self.position += used;
                Ok(n)
            }
            None => self.fail(self.position, Rejection::EndOfInput),
        }
    }

    /// Signed LEB128.
    pub(crate) fn signed(&mut self) -> Read<Signed> {
        match leb128::read_signed(self.rest()) {
            Some((n, used)) => {
                self.position += used;
                Ok(n)
            }
            None => self.fail(self.position, Rejection::EndOfInput),
        }
    }

    /// `n` bytes.
    pub(crate) fn bytes(&mut self, n: u64) -> Read<&'a [u8]> {
        let rest = self.rest();
        match usize::try_from(n).ok().filter(|&n| n <= rest.len()) {
            Some(n) => {
                self.position += n;
                Ok(&rest[..n])
            }
            None => self.fail(self.position, Rejection::EndOfInput),
        }
    }

    /// A blob: a length, then that many bytes.
    pub(crate) fn blob(&mut self) -> Read<&'a [u8]> {
        let n = self.unsigned()?;
        self.bytes(n)
    }

    /// Text: a blob that is UTF-8.
    pub(crate) fn text(&mut self) -> Read<&'a str> {
        let start = self.position;
        let blob = self.blob()?;
        match core::str::from_utf8(blob) {
            Ok(s) => Ok(s),
            Err(_) => self.fail(start, Rejection::TextNotUtf8),
        }
    }
}
