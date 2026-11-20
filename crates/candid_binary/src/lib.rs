//! Candid's binary format (`lean/Spec/Binary.md`): messages as bytes. A transcription of
//! `lean/Candid/Wire.lean`.
//!
//! A [`Decoder`] reads a message and an [`Encoder`] writes one. Each owns its position
//! in the message, so that the checks the spec asks of a whole message are theirs, not
//! their callers': an error position is always an offset in the whole message, an
//! encoder finishes a message only once every argument has its value, and a decoder will
//! reject bytes after the last value. So far they read and write only the [`Header`]:
//! the type table and the argument types. Values, and decoding them at the receiver's
//! types -- which is coercion (`lean/Spec/Types.md`, Section 6) -- come next.
//!
//! A message is read from a `&[u8]` and written to a `Vec<u8>`. A message always arrives
//! whole, and decoding needs all of it at hand: the `opt` rule goes back over bytes it
//! has read, and text and blobs can be handed out borrowed instead of copied. A
//! `Vec<u8>` turns into whatever a transport wants -- a slice, `bytes::Bytes` -- without
//! a copy.
//!
//! Every byte of a message comes from an untrusted sender. Nothing here allocates in
//! advance for a count the message gives, panics on any input, or recurses.
//!
//! No global state, no serde. `no_std`.

#![no_std]

extern crate alloc;

mod decoder;
mod encoder;
mod error;
mod header;
mod leb128;
mod reader;

pub use decoder::{Decoder, Limits};
pub use encoder::Encoder;
pub use error::{DecodeError, EncodeError, Rejection, UnresolvedArgument};
pub use header::Header;
