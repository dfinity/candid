//! This module provides functions to serialize and deserialize types
//! under [`std::rc::Rc`] shared reference type.
//!
//! # Examples
//!
//! ```
//! use candid::{CandidType, Deserialize};
//! use std::rc::Rc;
//!
//! #[derive(CandidType, Deserialize, PartialEq)]
//! struct RcString(#[serde(with = "candid::rc")] Rc<String>);
//! ```

use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::rc::Rc;

pub fn serialize<T: Serialize, S: Serializer>(
    data: &Rc<T>,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    T::serialize(data, serializer)
}

pub fn deserialize<'de, T: Deserialize<'de>, D: Deserializer<'de>>(
    deserializer: D,
) -> Result<Rc<T>, D::Error> {
    T::deserialize(deserializer).map(Rc::new)
}
