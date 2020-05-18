use crate::types::{CandidType, Serializer, Type, TypeId};
use num_bigint::{BigInt, BigUint};
use serde::de::{Deserialize, Visitor};
use std::convert::From;
use std::fmt;

#[derive(PartialEq, Debug)]
pub struct Int(BigInt);
#[derive(PartialEq, Debug)]
pub struct Nat(BigUint);

impl From<i64> for Int {
    fn from(v: i64) -> Self {
        Int(v.into())
    }
}

impl From<u64> for Nat {
    fn from(v: u64) -> Self {
        Nat(v.into())
    }
}

impl CandidType for Int {
    fn id() -> TypeId {
        TypeId::of::<Int>()
    }
    fn _ty() -> Type {
        Type::Int
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_int(&self.0.to_str_radix(10))
    }
}

impl CandidType for Nat {
    fn id() -> TypeId {
        TypeId::of::<Nat>()
    }
    fn _ty() -> Type {
        Type::Nat
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_nat(&self.0.to_str_radix(10))
    }
}

impl<'de> Deserialize<'de> for Int {
    fn deserialize<D>(deserializer: D) -> Result<Int, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct IntVisitor;
        impl<'de> Visitor<'de> for IntVisitor {
            type Value = Int;
            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("Int value")
            }
            fn visit_i64<E>(self, value: i64) -> Result<Int, E> {
                Ok(Int(value.into()))
            }
        }
        deserializer.deserialize_any(IntVisitor)
    }
}

impl<'de> Deserialize<'de> for Nat {
    fn deserialize<D>(deserializer: D) -> Result<Nat, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct NatVisitor;
        impl<'de> Visitor<'de> for NatVisitor {
            type Value = Nat;
            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("Nat value")
            }
            fn visit_u64<E>(self, value: u64) -> Result<Nat, E> {
                Ok(Nat(value.into()))
            }
        }
        deserializer.deserialize_any(NatVisitor)
    }
}
