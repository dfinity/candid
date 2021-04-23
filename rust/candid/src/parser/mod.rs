//! Provides parser for Candid type and value.
//!  * `str.parse::<IDLProg>()` parses the Candid signature file to Candid AST.
//!  * `str.parse::<IDLArgs>()` parses the Candid value in text format to a struct `IDLArg` that can be used for serialization and deserialization between Candid and an enum type `IDLValue` in Rust.

pub mod grammar;

pub mod token;
pub mod types;
pub mod value;

pub mod typing;

#[cfg(feature = "configs")]
pub mod configs;
pub mod pretty;
#[cfg(feature = "random")]
pub mod random;
pub mod test;
