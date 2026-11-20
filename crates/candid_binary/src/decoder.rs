//! Reading a message. Mirrors `decode` in `lean/Candid/Wire.lean`.

use core::fmt;

use crate::error::DecodeError;
use crate::header::Header;
use crate::reader::Reader;

/// A message being read: its header, and how far into its values reading has got.
///
/// A decoder borrows the whole message, so the values it hands out can borrow from it
/// rather than copy, and it can go back over bytes it has passed, as decoding at the
/// receiver's types has to. Every error position it reports is an offset in the whole
/// message.
///
/// So far it reads only the header. Decoding the values, and then checking that nothing
/// follows the last of them (`lean/Spec/Binary.md`, Section 4), come next.
pub struct Decoder<'a> {
    reader: Reader<'a>,
    header: Header,
}

impl<'a> Decoder<'a> {
    /// Start reading `message`: read and check its header.
    pub fn new(message: &'a [u8]) -> Result<Self, DecodeError> {
        let mut reader = Reader::new(message);
        let header = Header::decode(&mut reader)?;
        Ok(Decoder { reader, header })
    }

    /// The message's header: its type table and argument types.
    pub fn header(&self) -> &Header {
        &self.header
    }

    /// The offset in the message of the next byte to read.
    pub fn position(&self) -> usize {
        self.reader.position()
    }
}

impl fmt::Debug for Decoder<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Decoder")
            .field("header", &self.header)
            .field("position", &self.position())
            .finish_non_exhaustive()
    }
}
