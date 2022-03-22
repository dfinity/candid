//! Data structure for Candid value Func and Service

use super::{CandidType, Function, Serializer, Type};
use ic_types::Principal;
use serde::de::{self, Deserialize, Visitor};
use std::convert::TryFrom;
use std::{fmt, io::Read};

#[derive(PartialEq, Debug, Clone)]
pub struct Func {
    pub principal: Principal,
    pub method: String,
}
#[derive(PartialEq, Debug, Clone)]
pub struct Service {
    pub principal: Principal,
}

impl CandidType for Func {
    fn _ty() -> Type {
        Type::Func(Function {
            modes: Vec::new(),
            args: Vec::new(),
            rets: Vec::new(),
        })
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_function(self.principal.as_slice(), &self.method)
    }
}
impl CandidType for Service {
    fn _ty() -> Type {
        Type::Service(Vec::new())
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_principal(self.principal.as_slice())
    }
}

/// A [`Visitor`] to extract [`Func`]s.
pub struct FuncVisitor;

impl<'de> Visitor<'de> for FuncVisitor {
    type Value = Func;
    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("Func value")
    }
    fn visit_byte_buf<E: de::Error>(self, bytes: Vec<u8>) -> Result<Func, E> {
        if bytes[0] != 5u8 {
            return Err(de::Error::custom("not func"));
        }
        let mut bytes = &bytes[1..];
        let len = leb128::read::unsigned(&mut bytes).map_err(E::custom)? as usize;
        let mut buf = vec![0; len];
        bytes.read_exact(&mut buf).map_err(E::custom)?;
        let method = String::from_utf8(buf).map_err(E::custom)?;
        let principal = Principal::try_from(bytes).map_err(E::custom)?;
        Ok(Func { principal, method })
    }
}

impl<'de> Deserialize<'de> for Func {
    fn deserialize<D>(deserializer: D) -> Result<Func, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_any(FuncVisitor)
    }
}

impl<'de> Deserialize<'de> for Service {
    fn deserialize<D>(deserializer: D) -> Result<Service, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct ServVisitor;
        impl<'de> Visitor<'de> for ServVisitor {
            type Value = Service;
            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("Service value")
            }
            fn visit_byte_buf<E: de::Error>(self, bytes: Vec<u8>) -> Result<Service, E> {
                if bytes[0] != 4u8 {
                    return Err(de::Error::custom("not service"));
                }
                let bytes = &bytes[1..];
                let principal = Principal::try_from(bytes).map_err(E::custom)?;
                Ok(Service { principal })
            }
        }
        deserializer.deserialize_any(ServVisitor)
    }
}
