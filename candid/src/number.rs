//! Data structure for Candid Int and Nat types, supporting big integer with LEB128 encoding.

use crate::types::{CandidType, Serializer, Type, TypeId};
use crate::Error;
use num_bigint::{BigInt, BigUint};
use serde::de::{Deserialize, Visitor};
use std::convert::From;
use std::{fmt, io};

#[derive(PartialEq, Debug, Clone)]
pub struct Int(pub BigInt);
#[derive(PartialEq, Debug, Clone)]
pub struct Nat(pub BigUint);

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

impl Int {
    pub fn parse(v: &[u8]) -> crate::Result<Self> {
        let res = BigInt::parse_bytes(v, 10).ok_or_else(|| Error::msg("Cannot parse BigInt"))?;
        Ok(Int(res))
    }
}

impl Nat {
    pub fn parse(v: &[u8]) -> crate::Result<Self> {
        let res = BigUint::parse_bytes(v, 10).ok_or_else(|| Error::msg("Cannot parse BigUint"))?;
        Ok(Nat(res))
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
        serializer.serialize_int(self)
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
        serializer.serialize_nat(self)
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
            fn visit_bytes<E>(self, v: &[u8]) -> Result<Int, E> {
                Ok(Int(BigInt::from_signed_bytes_le(&v[1..])))
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
            fn visit_bytes<E>(self, v: &[u8]) -> Result<Nat, E> {
                Ok(Nat(BigUint::from_bytes_le(&v[1..])))
            }
        }
        deserializer.deserialize_any(NatVisitor)
    }
}

// LEB128 encoding for bignum.

impl Nat {
    pub fn encode<W>(&self, w: &mut W) -> crate::Result<()>
    where
        W: ?Sized + io::Write,
    {
        let zero = BigUint::from(0u8);
        let mut value = self.clone();
        loop {
            let big_byte = &value.0 & BigUint::from(0x7fu8);
            let mut byte = big_byte.to_bytes_le()[0];
            value.0 >>= 7;
            if value.0 != zero {
                byte |= 0x80u8;
            }
            let buf = [byte];
            w.write_all(&buf)?;
            if value.0 == zero {
                return Ok(());
            }
        }
    }
    pub fn decode<R>(r: &mut R) -> crate::Result<Self>
    where
        R: io::Read,
    {
        let mut result = BigUint::from(0u8);
        let mut shift = 0;
        loop {
            let mut buf = [0];
            r.read_exact(&mut buf)?;
            let low_bits = BigUint::from(buf[0] & 0x7fu8);
            result |= low_bits << shift;
            if buf[0] & 0x80u8 == 0 {
                return Ok(Nat(result));
            }
            shift += 7;
        }
    }
}

impl Int {
    pub fn encode<W>(&self, w: &mut W) -> crate::Result<()>
    where
        W: ?Sized + io::Write,
    {
        let zero = BigInt::from(0);
        let mut value = self.clone();
        loop {
            let big_byte = &value.0 & BigInt::from(0xff);
            let mut byte = big_byte.to_signed_bytes_le()[0];
            value.0 >>= 6;
            let done = value.0 == zero || value.0 == BigInt::from(-1);
            if done {
                byte &= 0x7f;
            } else {
                value.0 >>= 1;
                byte |= 0x80;
            }
            let buf = [byte];
            w.write_all(&buf)?;
            if done {
                return Ok(());
            }
        }
    }
    pub fn decode<R>(r: &mut R) -> crate::Result<Self>
    where
        R: io::Read,
    {
        let mut result = BigInt::from(0);
        let mut shift = 0;
        let mut byte;
        loop {
            let mut buf = [0];
            r.read_exact(&mut buf)?;
            byte = buf[0];
            let low_bits = BigInt::from(byte & 0x7fu8);
            result |= low_bits << shift;
            shift += 7;
            if byte & 0x80u8 == 0 {
                break;
            }
        }
        if shift % 8 != 0 && (0x40u8 & byte) == 0x40u8 {
            result |= BigInt::from(-1) << shift;
        }
        Ok(Int(result))
    }
}
