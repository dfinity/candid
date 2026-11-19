//! Candid's binary format (`lean/Spec/Binary.md`): messages as bytes. A transcription of
//! `lean/Candid/Wire.lean`.
//!
//! So far, the part of a message before its values: [`Header`] reads and writes the
//! type table and the argument types. Values, and decoding them at the receiver's types
//! -- which is coercion (`lean/Spec/Types.md`, Section 6) -- come next.
//!
//! Every byte of a message comes from an untrusted sender. Nothing here allocates in
//! advance for a count the message gives, panics on any input, or recurses.
//!
//! No global state, no serde. `no_std`.

#![no_std]

extern crate alloc;

mod error;
mod header;
mod leb128;
mod reader;

pub use error::{DecodeError, Rejection};
pub use header::Header;
