//! Candid bindings for different languages.
// This module assumes the input are type checked, it is safe to use unwrap.

// pub mod candid;
use ::candid::bindings::candid;

pub mod analysis;
pub mod javascript;
pub mod motoko;
pub mod rust;
pub mod typescript;
