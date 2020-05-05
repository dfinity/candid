extern crate leb128;
extern crate num_enum;
extern crate serde;

extern crate candid_derive;
pub use candid_derive::CandidType;
pub use serde::Deserialize;

pub mod types;
pub use types::CandidType;

pub mod error;
pub use error::{Error, Result};

pub mod parser;
pub use parser::types::IDLProg;
pub use parser::value::IDLArgs;

// IDL hash function comes from
// https://caml.inria.fr/pub/papers/garrigue-polymorphic_variants-ml98.pdf
pub fn idl_hash(id: &str) -> u32 {
    let mut s: u32 = 0;
    for c in id.chars() {
        s = s.wrapping_mul(223).wrapping_add(c as u32);
    }
    s
}
