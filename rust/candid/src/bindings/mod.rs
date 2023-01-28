//! Candid bindings for different languages.
// This module assumes the input are type checked, it is safe to use unwrap.

pub mod candid;

#[cfg(feature = "parser")]
pub mod analysis;
#[cfg(feature = "parser")]
pub mod javascript;
#[cfg(feature = "parser")]
pub mod motoko;
#[cfg(feature = "parser")]
pub mod rust;
#[cfg(feature = "parser")]
pub mod typescript;
