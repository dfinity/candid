//! Data structure for Candid value Func and Service
//! Note that `Func` and `Service` should not be used directly. We need to define a newtype for `Func` or `Service`,
//! and manually `impl CandidType` for the newtype, in order to specify the correct reference type.
//! We have two macros `define_function!` and `define_service!` to help defining the newtype.

use super::principal::Principal;
use super::{CandidType, Serializer, Type};
use serde::de::{self, Deserialize, Visitor};
use std::convert::TryFrom;
use std::{fmt, io::Read};

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Func {
    pub principal: Principal,
    pub method: String,
}
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Service {
    pub principal: Principal,
}

#[macro_export]
/// Define a function reference type.
/// `define_function!(FuncReference : func!(() -> () query))`
macro_rules! define_function {
    ( $vis:vis $func:ident : $ty:expr ) => {
        #[derive(Deserialize, PartialEq, Debug, Clone)]
        $vis struct $func(pub Func);
        impl CandidType for $func {
            fn _ty() -> $crate::types::Type {
                $ty
            }
            fn idl_serialize<S: $crate::types::Serializer>(&self, serializer: S) -> Result<(), S::Error>
            {
                self.0.idl_serialize(serializer)
            }
        }
    }
}
#[macro_export]
/// Define a service reference type.
macro_rules! define_service {
    ( $vis:vis $serv:ident : $ty:expr ) => {
        #[derive(Deserialize, PartialEq, Debug, Clone)]
        $vis struct $serv(pub Service);
        impl CandidType for $serv {
            fn _ty() -> $crate::types::Type {
                $ty
            }
            fn idl_serialize<S: $crate::types::Serializer>(&self, serializer: S) -> Result<(), S::Error>
            {
                self.0.idl_serialize(serializer)
            }
        }
    }
}

impl CandidType for Func {
    fn _ty() -> Type {
        panic!("Cannot use Func directly. Use `define_function!` macro instead.")
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
        panic!("Cannot use Service directly. Use `define_service!` macro instead.")
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
