//! This module provides functions to serialize and deserialize types
//! under [`std::sync::Arc`] shared reference type.
//!
//! # Examples
//!
//! ```
//! use candid::{CandidType, Deserialize};
//! use std::sync::Arc;
//!
//! #[derive(CandidType, Deserialize, PartialEq)]
//! struct ArcString(#[serde(with = "candid::arc")] Arc<String>);
//! ```
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::sync::Arc;

pub fn serialize<T: Serialize, S: Serializer>(
    data: &Arc<T>,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    T::serialize(data, serializer)
}

pub fn deserialize<'de, T: Deserialize<'de>, D: Deserializer<'de>>(
    deserializer: D,
) -> Result<Arc<T>, D::Error> {
    T::deserialize(deserializer).map(Arc::new)
}
