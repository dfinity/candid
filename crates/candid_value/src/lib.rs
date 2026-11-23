//! Candid's dynamic value (`lean/Spec/Types.md`, Section 4): any value of any Candid type,
//! as a [`Value`]. A transcription of `lean/Candid/Value.lean`.
//!
//! A value goes into a message through [`candid_binary::Encode`], which [`Value`]
//! implements: written at a type, it is checked against it. Reading one back, at the
//! receiver's types, comes with decoding values in `candid_binary`.
//!
//! `nat` and `int` are [`Nat`] and [`Int`], of any size; principals are
//! [`ic_principal::Principal`]. Printing and parsing values as text is `candid_syntax`'s.
//!
//! No global state, no serde.

mod number;
mod value;

pub use ic_principal::Principal;
pub use number::{Int, Nat, OutOfRange, ParseNumberError};
pub use value::{DuplicateField, Float32, Float64, Record, Value};
