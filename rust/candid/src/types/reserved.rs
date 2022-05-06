//! Data structure for Candid type Reserved and Empty.

use super::{CandidType, Serializer, Type, TypeId};
use serde::de::{self, Deserialize, Deserializer, Visitor};
use std::fmt;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Reserved;
#[derive(PartialEq, Debug)]
pub enum Empty {}

impl CandidType for Reserved {
    fn id() -> TypeId {
        TypeId::of::<Reserved>()
    }
    fn _ty() -> Type {
        Type::Reserved
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_null(())
    }
}

impl CandidType for Empty {
    fn id() -> TypeId {
        TypeId::of::<Empty>()
    }
    fn _ty() -> Type {
        Type::Empty
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_empty()
    }
}

impl<'de> Deserialize<'de> for Reserved {
    fn deserialize<D>(deserializer: D) -> Result<Reserved, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer
            .deserialize_ignored_any(de::IgnoredAny)
            .map(|_| Reserved)
    }
}

impl<'de> Deserialize<'de> for Empty {
    fn deserialize<D>(deserializer: D) -> Result<Empty, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct EmptyVisitor;
        impl<'de> Visitor<'de> for EmptyVisitor {
            type Value = Empty;
            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("Cannot decode empty value")
            }
        }
        deserializer.deserialize_any(EmptyVisitor)
    }
}
