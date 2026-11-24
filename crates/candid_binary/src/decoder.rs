//! Reading a message, at the receiver's types. Mirrors `decodeAt` in
//! `lean/Candid/DecodeAt.lean`.

use core::fmt;

use candid_types::Root;

use crate::cursor::{Cursor, Pending};
use crate::error::{DecodeError, Rejection};
use crate::header::Header;
use crate::reader::Reader;
use crate::value_reader::{Decode, ValueReader};

/// A message being read: its header, then its values, one argument at a time, each at
/// the receiver's type for it.
///
/// ```
/// # use candid_binary::{Decoder, Encoder, Header};
/// # use candid_types::{Slot, TypeTable};
/// let header = Header::new(TypeTable::default(), vec![Slot::NAT]).unwrap();
/// let mut encoder = Encoder::new(header);
/// encoder.argument()?.nat(&[5])?;
/// let bytes = encoder.finish()?;
///
/// // Read at `(int, opt text)`: a `nat` coerces to `int`, and a missing `opt` is `null`.
/// let receiver = Header::new(TypeTable::default(), vec![Slot::INT]).unwrap();
/// let mut decoder = Decoder::new(&bytes).unwrap();
/// let n = decoder.argument_with(receiver.table().root(Slot::INT).unwrap(), |r| r.int()).unwrap();
/// assert_eq!(n.and_then(|n| n.to_i64()), Some(5));
/// decoder.finish().unwrap();
/// # Ok::<(), candid_binary::EncodeError>(())
/// ```
///
/// A decoder borrows the whole message, so the values it hands out can borrow from it
/// rather than copy. It reads each byte once, and never goes back. Every error position it
/// reports is an offset in the whole message.
///
/// It spends no more on a message than its [`Limits`] allow.
pub struct Decoder<'a> {
    cursor: Cursor<'a>,
    header: Header,
    /// How many of the sender's arguments have been read.
    next: usize,
    /// Whether an argument has failed to coerce. That decides the message: nothing more
    /// of it is read at the receiver's types.
    failed: bool,
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
        Ok(Decoder {
            cursor: Cursor::new(reader, limits),
            header,
            next: 0,
            failed: false,
        })
    }

    /// The message's header: its type table and argument types.
    pub fn header(&self) -> &Header {
        &self.header
    }

    /// The offset in the message of the next byte to read.
    pub fn position(&self) -> usize {
        self.cursor.position()
    }

    /// The next argument, read as a `T` at the receiver's type `expected`.
    ///
    /// Past the sender's last argument, the value is missing: `null` if `expected` accepts
    /// it, a failure if not (`lean/Spec/Types.md`, Section 6.8). `Ok(None)` is a failure,
    /// and rejects the message: once one argument has failed, every later one is
    /// `Ok(None)` too, and is not read at the receiver's types.
    pub fn argument<T: Decode<'a>>(
        &mut self,
        expected: Root<'_>,
    ) -> Result<Option<T>, DecodeError> {
        self.argument_with(expected, T::try_decode)
    }

    /// The next argument, read by `read` at the receiver's type `expected`: as
    /// [`Decoder::argument`], for a receiver that is a closure rather than a type.
    pub fn argument_with<T>(
        &mut self,
        expected: Root<'_>,
        read: impl FnOnce(ValueReader<'_, 'a>) -> Result<Option<T>, DecodeError>,
    ) -> Result<Option<T>, DecodeError> {
        if self.failed {
            return Ok(None);
        }
        let value = self.header.types().get(self.next).map(|&slot| {
            self.next += 1;
            Pending { slot, stall: 0 }
        });
        self.cursor.new_receiver();
        let table = self.header.table();
        let v = read(ValueReader::new(&mut self.cursor, table, value, expected))?;
        self.cursor.settle(table)?;
        if v.is_none() {
            self.failed = true;
        }
        if let Some(at) = self.cursor.undefined {
            // An undefined argument is the message's answer, once the rest of the message
            // has been read without an error.
            self.skip_rest()?;
            return Err(DecodeError::new(at, Rejection::InfiniteOption));
        }
        Ok(v)
    }

    /// Skip the arguments not read, which are checked and counted all the same, then
    /// check that no bytes follow the last value.
    fn skip_rest(&mut self) -> Result<(), DecodeError> {
        let table = self.header.table();
        for &slot in &self.header.types()[self.next..] {
            self.cursor.skip(table, Pending { slot, stall: 0 })?;
        }
        self.next = self.header.types().len();
        if self.cursor.reader.rest().is_empty() {
            Ok(())
        } else {
            self.cursor.fail(Rejection::BytesAfterValues)
        }
    }

    /// The end of the message: skip the arguments not read, which are checked and
    /// counted all the same, then check that no bytes follow the last value.
    pub fn finish(mut self) -> Result<(), DecodeError> {
        self.skip_rest()
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
    /// The most values the message may stand for, counting every value wherever it is:
    /// inside another, skipped, past the expected arguments -- as Lean's `limit` counts
    /// them (`lean/Candid/Wire.lean`, "Costly messages").
    ///
    /// A value of `null`, `reserved` or a record of them takes no bytes, so this is what
    /// bounds the time a short message takes, and a receiver's memory. A blob counts a
    /// value per byte. The default is 2^22, twice the bytes of the largest message the
    /// Internet Computer carries.
    pub values: u64,
    /// The deepest values may nest in what the receiver builds: in an `opt`, a `vec`, a
    /// record or a variant. A receiver nests as the values do, on the stack. Skipping a
    /// value does not nest. The default is 1024.
    pub depth: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Limits {
            header_bytes: 64 * 1024,
            values: 1 << 22,
            depth: 1024,
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
        Limits {
            header_bytes,
            ..Limits::default()
        }
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
