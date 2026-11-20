//! Writing a message. Mirrors `encode` in `lean/Candid/Wire.lean`.

use alloc::vec::Vec;

use crate::error::EncodeError;
use crate::header::Header;

/// A message being written: its header, then a value for each argument type in order.
///
/// So far it writes only the header, so only a message with no arguments can be
/// finished. Writing values comes next.
#[derive(Clone, Debug)]
pub struct Encoder {
    out: Vec<u8>,
    header: Header,
    /// How many values have been written.
    written: usize,
}

impl Encoder {
    /// Start a message with this header.
    pub fn new(header: Header) -> Self {
        Encoder::with_buffer(header, Vec::new())
    }

    /// Start a message with this header, appended to `out`: reusing a buffer saves an
    /// allocation per message. Whatever `out` already holds is kept, in front of the
    /// message, so clear it first unless it is meant to be a prefix.
    pub fn with_buffer(header: Header, mut out: Vec<u8>) -> Self {
        header.encode(&mut out);
        Encoder {
            out,
            header,
            written: 0,
        }
    }

    /// The message's header.
    pub fn header(&self) -> &Header {
        &self.header
    }

    /// The finished message, once every argument has its value.
    pub fn finish(self) -> Result<Vec<u8>, EncodeError> {
        let expected = self.header.types().len();
        if self.written < expected {
            return Err(EncodeError::MissingArguments {
                expected,
                written: self.written,
            });
        }
        Ok(self.out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Decoder;
    use alloc::vec;
    use candid_types::{Slot, TypeTable};

    #[test]
    fn a_message_with_no_arguments() {
        let header = Header::new(TypeTable::default(), vec![]).unwrap();
        let bytes = Encoder::new(header.clone()).finish().unwrap();
        assert_eq!(bytes, b"DIDL\x00\x00");
        let decoder = Decoder::new(&bytes).unwrap();
        assert_eq!((decoder.header(), decoder.position()), (&header, 6));
    }

    #[test]
    fn a_buffer_is_appended_to() {
        let header = Header::new(TypeTable::default(), vec![]).unwrap();
        let bytes = Encoder::with_buffer(header, b"x".to_vec())
            .finish()
            .unwrap();
        assert_eq!(bytes, b"xDIDL\x00\x00");
    }

    #[test]
    fn every_argument_needs_a_value() {
        let header = Header::new(TypeTable::default(), vec![Slot::NAT]).unwrap();
        assert_eq!(
            Encoder::new(header).finish(),
            Err(EncodeError::MissingArguments {
                expected: 1,
                written: 0
            })
        );
    }
}
