//! Data structure for Candid type Reserved and Empty.

use super::{CandidType, Serializer, Type, TypeInner};
use serde::de::{self, Deserialize, Deserializer, Visitor};
use serde::Serialize;
use std::fmt;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, PartialOrd, Ord, Hash, Serialize)]
pub struct Reserved;
#[derive(PartialEq, Eq, Debug)]
pub enum Empty {}

impl CandidType for Reserved {
    fn _ty() -> Type {
        TypeInner::Reserved.into()
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_null(())
    }
}

impl CandidType for Empty {
    fn _ty() -> Type {
        TypeInner::Empty.into()
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
        impl Visitor<'_> for EmptyVisitor {
            type Value = Empty;
            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("Cannot decode empty value")
            }
        }
        deserializer.deserialize_any(EmptyVisitor)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::Deserialize;

    #[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
    pub struct TestStruct {
        inner: Reserved,
    }

    #[test]
    fn test_serde_with_json() {
        let test_struct = TestStruct { inner: Reserved };
        let serialized = serde_json::to_string(&test_struct).unwrap();
        let deserialized = serde_json::from_str(&serialized).unwrap();
        assert_eq!(test_struct, deserialized);
    }
}
