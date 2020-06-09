use crate::types::{CandidType, Serializer, Type, TypeId};
use serde::de::{Deserialize, Visitor};

#[derive(PartialEq, Debug)]
pub struct Principal(pub Vec<u8>);

impl CandidType for Principal {
    fn id() -> TypeId {
        TypeId::of::<Principal>()
    }
    fn _ty() -> Type {
        Type::Principal
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_principal(&self.0)
    }
}

impl<'de> Deserialize<'de> for Principal {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct PrincipalVisitor;
        impl<'de> Visitor<'de> for PrincipalVisitor {
            type Value = Principal;
            fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                formatter.write_str("Principal value")
            }
            fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E> {
                Ok(Principal(v[1..].to_vec()))
            }
        }
        deserializer.deserialize_any(PrincipalVisitor)
    }
}
