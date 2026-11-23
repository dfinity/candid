//! Candid's binary format (`lean/Spec/Binary.md`): messages as bytes. A transcription of
//! `lean/Candid/Wire.lean`.
//!
//! A [`Decoder`] reads a message and an [`Encoder`] writes one. Each owns its position
//! in the message, so that the checks the spec asks of a whole message are theirs, not
//! their callers': an error position is always an offset in the whole message, an
//! encoder finishes a message only once every argument has its value, and a decoder will
//! reject bytes after the last value. A message starts with its [`Header`]: the type
//! table and the argument types. An encoder then writes a value for each argument, through
//! a [`ValueWriter`], which a type drives by implementing [`Encode`]. A decoder reads each
//! argument at the receiver's type for it, through a [`ValueReader`], which a type drives
//! by implementing [`Decode`]: that is coercion (`lean/Spec/Types.md`, Section 6), done
//! while reading, as `decodeAt` of `lean/Candid/DecodeAt.lean` does it.
//!
//! A message is read from a `&[u8]` and written to a `Vec<u8>`. A message always arrives
//! whole, and the decoder takes all of it at once: text and blobs can be handed out
//! borrowed instead of copied. A
//! `Vec<u8>` turns into whatever a transport wants -- a slice, `bytes::Bytes` -- without
//! a copy.
//!
//! Every byte of a message comes from an untrusted sender. Nothing here allocates in
//! advance for a count the message gives, or panics on any input. Nothing recurses as
//! deep as the sender chooses: skipping a value is a loop, and a receiver nests only as
//! deep as [`Limits::depth`].
//!
//! No global state, no serde. `no_std`.

#![no_std]

extern crate alloc;

mod cursor;
mod decoder;
mod encoder;
mod error;
mod header;
mod leb128;
mod reader;
mod value_reader;
mod writer;

pub use decoder::{Decoder, Limits};
pub use encoder::Encoder;
pub use error::{DecodeError, EncodeError, Rejection, UnresolvedArgument};
pub use header::Header;
pub use value_reader::{Decode, Integer, Natural, RecordReader, ValueReader};
pub use writer::{Encode, RecordWriter, ValueWriter, VecWriter};
