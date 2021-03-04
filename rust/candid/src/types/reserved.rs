//! Data structure for Candid type Reserved and Empty.

use super::{CandidType, Serializer, Type, TypeId};
use serde::de::{self, Deserialize, Deserializer, Visitor};
use std::fmt;

#[derive(PartialEq, Debug, Clone)]
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
        struct ReservedVisitor;
        impl<'de> Visitor<'de> for ReservedVisitor {
            type Value = Reserved;
            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("Reserved value")
            }
            fn visit_bool<E>(self, _: bool) -> Result<Reserved, E> {
                Ok(Reserved)
            }
            fn visit_i64<E>(self, _: i64) -> Result<Reserved, E> {
                Ok(Reserved)
            }
            fn visit_u64<E>(self, _: u64) -> Result<Reserved, E> {
                Ok(Reserved)
            }
            fn visit_i128<E>(self, _: i128) -> Result<Reserved, E> {
                Ok(Reserved)
            }
            fn visit_u128<E>(self, _: u128) -> Result<Reserved, E> {
                Ok(Reserved)
            }
            fn visit_f64<E>(self, _: f64) -> Result<Reserved, E> {
                Ok(Reserved)
            }
            fn visit_str<E>(self, _: &str) -> Result<Reserved, E> {
                Ok(Reserved)
            }
            fn visit_bytes<E>(self, _v: &[u8]) -> Result<Reserved, E> {
                Ok(Reserved)
            }
            fn visit_none<E>(self) -> Result<Reserved, E> {
                Ok(Reserved)
            }
            fn visit_some<D: Deserializer<'de>>(self, d: D) -> Result<Reserved, D::Error> {
                Reserved::deserialize(d)
            }
            fn visit_unit<E>(self) -> Result<Reserved, E> {
                Ok(Reserved)
            }
            fn visit_newtype_struct<D: Deserializer<'de>>(
                self,
                d: D,
            ) -> Result<Reserved, D::Error> {
                Reserved::deserialize(d)
            }
            fn visit_seq<A: de::SeqAccess<'de>>(self, mut seq: A) -> Result<Reserved, A::Error> {
                while let Some(Reserved) = seq.next_element()? {}
                Ok(Reserved)
            }
            fn visit_map<A: de::MapAccess<'de>>(self, mut map: A) -> Result<Reserved, A::Error> {
                while let Some((Reserved, Reserved)) = map.next_entry()? {}
                Ok(Reserved)
            }
            fn visit_enum<A: de::EnumAccess<'de>>(self, data: A) -> Result<Reserved, A::Error> {
                use serde::de::VariantAccess;
                data.variant::<Reserved>()?.1.newtype_variant()
            }
        }
        deserializer.deserialize_ignored_any(ReservedVisitor)
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
