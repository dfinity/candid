//! Data structure for Candid type Reserved and Empty.

use crate::types::{CandidType, Serializer, Type, TypeId};
use serde::de::{Deserialize, Visitor};
use std::fmt;

#[derive(PartialEq, Debug)]
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
        D: serde::Deserializer<'de>,
    {
        struct ReservedVisitor;
        impl<'de> Visitor<'de> for ReservedVisitor {
            type Value = Reserved;
            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("Reserved value")
            }
            fn visit_unit<E>(self) -> Result<Reserved, E> {
                Ok(Reserved)
            }
        }
        deserializer.deserialize_any(ReservedVisitor)
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
                formatter.write_str("Empty value")
            }
        }
        deserializer.deserialize_any(EmptyVisitor)
    }
}
