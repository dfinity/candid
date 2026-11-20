//! Reading a message. Mirrors `decode` in `lean/Candid/Wire.lean`.

use core::fmt;

use crate::error::{DecodeError, Rejection};
use crate::header::Header;
use crate::reader::Reader;

/// A message being read: its header, and how far into its values reading has got.
///
/// A decoder borrows the whole message, so the values it hands out can borrow from it
/// rather than copy, and it can go back over bytes it has passed, as decoding at the
/// receiver's types has to. Every error position it reports is an offset in the whole
/// message.
///
/// It spends no more on a message than its [`Limits`] allow. So far it reads only the
/// header. Decoding the values, and then checking that nothing
/// follows the last of them (`lean/Spec/Binary.md`, Section 4), come next.
pub struct Decoder<'a> {
    reader: Reader<'a>,
    header: Header,
}

impl<'a> Decoder<'a> {
    /// Start reading `message`: read and check its header, within the default
    /// [`Limits`].
    pub fn new(message: &'a [u8]) -> Result<Self, DecodeError> {
        Decoder::with_limits(message, Limits::default())
    }

    /// Start reading `message` within `limits`: read and check its header.
    pub fn with_limits(message: &'a [u8], limits: Limits) -> Result<Self, DecodeError> {
        // The header is read from a prefix no longer than the limit, so a header that
        // claims more costs the limit, not what it claims.
        let bound = message.len().min(limits.header_bytes);
        let mut prefix = Reader::new(&message[..bound]);
        let header = match Header::decode(&mut prefix) {
            Ok(header) => header,
            // Running out inside a cut prefix is running into the limit. Any other
            // rejection the header earns before the limit, it keeps.
            Err(e) if bound < message.len() && *e.rejection() == Rejection::EndOfInput => {
                return Err(DecodeError::new(bound, Rejection::HeaderTooLarge));
            }
            Err(e) => return Err(e),
        };
        let reader = Reader::starting_at(message, prefix.position());
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

/// How much a [`Decoder`] will spend on one message. Anything over a limit is rejected
/// as a resource limit (`lean/Spec/Binary.md`, Section 9; see
/// [`Rejection::is_resource_limit`]), never accepted in part.
///
/// The spec sets no limits: what a receiver can afford depends on where it runs. The
/// defaults are generous for any real interface.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[non_exhaustive]
pub struct Limits {
    /// The most bytes the header -- the magic number, the type table and the argument
    /// types -- may take. The values after it are not counted.
    ///
    /// A header takes some tens of times its length in memory once read, so this is
    /// what bounds that memory. The default is 64 KiB.
    pub header_bytes: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Limits {
            header_bytes: 64 * 1024,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec::Vec;

    /// A header of `n` entries `opt nat`, each two bytes, and no arguments.
    fn opt_nats(n: usize) -> Vec<u8> {
        let mut m = b"DIDL".to_vec();
        crate::leb128::write_unsigned(&mut m, n as u64);
        for _ in 0..n {
            m.extend_from_slice(&[0x6e, 0x7d]);
        }
        m.push(0x00);
        m
    }

    fn limit(header_bytes: usize) -> Limits {
        Limits { header_bytes }
    }

    #[test]
    fn a_header_within_the_limit() {
        let m = opt_nats(100);
        let d = Decoder::with_limits(&m, limit(m.len())).unwrap();
        assert_eq!((d.header().table().len(), d.position()), (100, m.len()));
    }

    #[test]
    fn a_header_over_the_limit() {
        let mut m = opt_nats(100);
        let header = m.len();
        m.push(0xaa); // a value, which the limit does not count
        assert!(Decoder::with_limits(&m, limit(header)).is_ok());
        let e = Decoder::with_limits(&m, limit(header - 1)).unwrap_err();
        assert_eq!(
            (e.position(), e.rejection()),
            (header - 1, &Rejection::HeaderTooLarge)
        );
        assert!(e.rejection().is_resource_limit());
        // A large default still stops a large header.
        let m = opt_nats(40_000);
        let e = Decoder::new(&m).unwrap_err();
        assert_eq!(e.rejection(), &Rejection::HeaderTooLarge);
    }

    #[test]
    fn a_header_that_is_cut_short_is_not_over_the_limit() {
        let m = opt_nats(100);
        let cut = &m[..m.len() - 1];
        let e = Decoder::with_limits(cut, limit(m.len())).unwrap_err();
        assert_eq!(e.rejection(), &Rejection::EndOfInput);
        // Nor is a header that is wrong before the limit.
        let e = Decoder::with_limits(b"DIDMxxxx", limit(5)).unwrap_err();
        assert_eq!(e.rejection(), &Rejection::MissingMagicNumber);
    }
}
