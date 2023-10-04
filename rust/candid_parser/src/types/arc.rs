//! This module provides functions to serialize and deserialize types
//! under [std::sync::Arc] shared reference type.
//!
//! # Examples
//!
//! ```
//! use candid::{CandidType, Deserialize};
//! use serde_bytes::ByteBuf;
//! use std::sync::Arc;
//!
//! #[derive(CandidType, Deserialize, PartialEq)]
//! struct ArcBytes(#[serde(with = "candid::arc")] Arc<ByteBuf>);
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
