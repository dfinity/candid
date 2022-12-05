//! Data structure for Candid type Int, Nat, supporting big integer with LEB128 encoding.

use super::{CandidType, Serializer, Type, TypeId};
use crate::Error;
use num_bigint::{BigInt, BigUint};
use serde::{
    de::{self, Deserialize, Visitor},
    Serialize,
};
use std::convert::From;
use std::{fmt, io};

#[derive(Serialize, Ord, PartialOrd, Eq, PartialEq, Debug, Clone, Hash, Default)]
pub struct Int(pub BigInt);
#[derive(Serialize, Ord, PartialOrd, Eq, PartialEq, Debug, Clone, Hash, Default)]
pub struct Nat(pub BigUint);

impl From<BigInt> for Int {
    #[inline(always)]
    fn from(i: BigInt) -> Self {
        Self(i)
    }
}

impl From<BigUint> for Nat {
    #[inline(always)]
    fn from(i: BigUint) -> Self {
        Self(i)
    }
}

impl From<Nat> for Int {
    #[inline(always)]
    fn from(n: Nat) -> Self {
        let i: BigInt = n.0.into();
        i.into()
    }
}

impl From<Int> for BigInt {
    #[inline(always)]
    fn from(i: Int) -> Self {
        i.0
    }
}

impl From<Nat> for BigUint {
    #[inline(always)]
    fn from(i: Nat) -> Self {
        i.0
    }
}

impl From<Nat> for BigInt {
    #[inline(always)]
    fn from(i: Nat) -> Self {
        i.0.into()
    }
}

impl Int {
    #[inline]
    pub fn parse(v: &[u8]) -> crate::Result<Self> {
        let res = BigInt::parse_bytes(v, 10).ok_or_else(|| Error::msg("Cannot parse BigInt"))?;
        Ok(Int(res))
    }
}

impl Nat {
    #[inline]
    pub fn parse(v: &[u8]) -> crate::Result<Self> {
        let res = BigUint::parse_bytes(v, 10).ok_or_else(|| Error::msg("Cannot parse BigUint"))?;
        Ok(Nat(res))
    }
}

impl std::str::FromStr for Int {
    type Err = crate::Error;
    fn from_str(str: &str) -> Result<Self, Self::Err> {
        Self::parse(str.as_bytes())
    }
}

impl std::str::FromStr for Nat {
    type Err = crate::Error;
    fn from_str(str: &str) -> Result<Self, Self::Err> {
        Self::parse(str.as_bytes())
    }
}

pub(crate) fn pp_num_str(s: &str) -> String {
    let mut groups = Vec::new();
    for chunk in s.as_bytes().rchunks(3) {
        let str = String::from_utf8_lossy(chunk);
        groups.push(str);
    }
    groups.reverse();
    if "-" == groups.first().unwrap() {
        "-".to_string() + &groups[1..].join("_")
    } else {
        groups.join("_")
    }
}

impl fmt::Display for Int {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = self.0.to_str_radix(10);
        f.write_str(&pp_num_str(&s))
    }
}

impl fmt::Display for Nat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = self.0.to_str_radix(10);
        f.write_str(&pp_num_str(&s))
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
            fn visit_i64<E>(self, v: i64) -> Result<Int, E> {
                Ok(Int::from(v))
            }
            fn visit_u64<E>(self, v: u64) -> Result<Int, E> {
                Ok(Int::from(v))
            }
            fn visit_str<E: de::Error>(self, v: &str) -> Result<Int, E> {
                v.parse::<Int>()
                    .map_err(|_| de::Error::custom(format!("{:?} is not int", v)))
            }
            fn visit_byte_buf<E: de::Error>(self, v: Vec<u8>) -> Result<Int, E> {
                Ok(Int(match v[0] {
                    0 => BigInt::from_signed_bytes_le(&v[1..]),
                    1 => BigInt::from_biguint(
                        num_bigint::Sign::Plus,
                        BigUint::from_bytes_le(&v[1..]),
                    ),
                    _ => return Err(de::Error::custom("not int nor nat")),
                }))
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
            fn visit_i64<E: de::Error>(self, v: i64) -> Result<Nat, E> {
                use std::convert::TryFrom;
                Ok(Nat(BigUint::try_from(v).map_err(|_| {
                    de::Error::custom("int cannot be converted to nat")
                })?))
            }
            fn visit_u64<E>(self, v: u64) -> Result<Nat, E> {
                Ok(Nat::from(v))
            }
            fn visit_str<E: de::Error>(self, v: &str) -> Result<Nat, E> {
                v.parse::<Nat>()
                    .map_err(|_| de::Error::custom(format!("{:?} is not nat", v)))
            }
            fn visit_byte_buf<E: de::Error>(self, v: Vec<u8>) -> Result<Nat, E> {
                if v[0] == 1 {
                    Ok(Nat(BigUint::from_bytes_le(&v[1..])))
                } else {
                    Err(de::Error::custom("not nat"))
                }
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
        use num_traits::cast::ToPrimitive;
        let zero = BigUint::from(0u8);
        let mut value = self.0.clone();
        loop {
            let big_byte = &value & BigUint::from(0x7fu8);
            let mut byte = big_byte.to_u8().unwrap();
            value >>= 7;
            if value != zero {
                byte |= 0x80u8;
            }
            let buf = [byte];
            w.write_all(&buf)?;
            if value == zero {
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
        use num_traits::cast::ToPrimitive;
        let zero = BigInt::from(0);
        let mut value = self.0.clone();
        loop {
            let big_byte = &value & BigInt::from(0xff);
            let mut byte = big_byte.to_u8().unwrap();
            value >>= 6;
            let done = value == zero || value == BigInt::from(-1);
            if done {
                byte &= 0x7f;
            } else {
                value >>= 1;
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
        if (0x40u8 & byte) == 0x40u8 {
            result |= BigInt::from(-1) << shift;
        }
        Ok(Int(result))
    }
}

// Define all operators and traits relevant for Nat and Int.
use std::cmp::{Ord, Ordering, PartialEq, PartialOrd};
use std::ops::*;

macro_rules! define_from {
    ($f: ty, $($t: ty)*) => ($(
        impl From<$t> for $f {
            #[inline]
            fn from(v: $t) -> Self { Self(v.into()) }
        }
    )*)
}

macro_rules! define_eq {
    ($f: ty, $($t: ty)*) => ($(
        impl PartialEq<$t> for $f {
            #[inline]
            #[must_use]
            fn eq(&self, v: &$t) -> bool { self.0.eq(&(*v).into()) }
        }
        impl PartialEq<$f> for $t {
            #[inline]
            #[must_use]
            fn eq(&self, v: &$f) -> bool { v.0.eq(&(*self).into()) }
        }
    )*)
}

macro_rules! define_op {
    (impl $imp: ident < $scalar: ty > for $res: ty, $method: ident) => {
        // Implement A * B
        impl $imp<$scalar> for $res {
            type Output = $res;

            #[inline]
            fn $method(self, other: $scalar) -> $res {
                $imp::$method(self.0, &other).into()
            }
        }

        // Implement B * A
        impl $imp<$res> for $scalar {
            type Output = $res;

            #[inline]
            fn $method(self, other: $res) -> $res {
                $imp::$method(other.0, &self).into()
            }
        }
    };
}

macro_rules! define_ord {
    ($scalar: ty, $res: ty) => {
        // A < B
        impl PartialOrd<$scalar> for $res {
            #[inline]
            fn partial_cmp(&self, other: &$scalar) -> Option<Ordering> {
                PartialOrd::partial_cmp(self, &<$res>::from(*other))
            }
        }
        // B < A
        impl PartialOrd<$res> for $scalar {
            #[inline]
            fn partial_cmp(&self, other: &$res) -> Option<Ordering> {
                PartialOrd::partial_cmp(&<$res>::from(*self), other)
            }
        }
    };
}

macro_rules! define_op_assign {
    (impl $imp: ident < $scalar: ty > for $res: ty, $method: ident) => {
        // Implement A * B
        impl $imp<$scalar> for $res {
            #[inline]
            fn $method(&mut self, other: $scalar) {
                $imp::$method(&mut self.0, other)
            }
        }
    };
}

macro_rules! define_ops {
    ($f: ty, $($t: ty)*) => ($(
        define_op!(impl Add<$t> for $f, add);
        define_op!(impl Sub<$t> for $f, sub);
        define_op!(impl Mul<$t> for $f, mul);
        define_op!(impl Div<$t> for $f, div);
        define_op!(impl Rem<$t> for $f, rem);

        define_ord!($t, $f);

        define_op_assign!(impl AddAssign<$t> for $f, add_assign);
        define_op_assign!(impl SubAssign<$t> for $f, sub_assign);
        define_op_assign!(impl MulAssign<$t> for $f, mul_assign);
        define_op_assign!(impl DivAssign<$t> for $f, div_assign);
        define_op_assign!(impl RemAssign<$t> for $f, rem_assign);
    )*)
}

define_from!( Nat, usize u8 u16 u32 u64 u128 );
define_from!( Int, usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128 );

define_eq!( Nat, usize u8 u16 u32 u64 u128 );
define_eq!( Int, usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128 );

define_ops!( Nat, usize u8 u16 u32 u64 u128 );
define_ops!( Int, usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128 );

// Need a separate macro to extract the Big[U]Int from the Nat/Int struct.
macro_rules! define_op_0 {
    (impl $imp: ident < $scalar: ty > for $res: ty, $method: ident) => {
        impl $imp<$scalar> for $res {
            type Output = $res;

            #[inline]
            fn $method(self, other: $scalar) -> $res {
                $imp::$method(self.0, &other.0).into()
            }
        }
    };
}

macro_rules! define_op_0_assign {
    (impl $imp: ident < $scalar: ty > for $res: ty, $method: ident) => {
        // Implement A * B
        impl $imp<$scalar> for $res {
            #[inline]
            fn $method(&mut self, other: $scalar) {
                $imp::$method(&mut self.0, other.0)
            }
        }
    };
}

define_op_0!(impl Add<Nat> for Nat, add);
define_op_0!(impl Sub<Nat> for Nat, sub);
define_op_0!(impl Mul<Nat> for Nat, mul);
define_op_0!(impl Div<Nat> for Nat, div);
define_op_0!(impl Rem<Nat> for Nat, rem);

define_op_0_assign!(impl AddAssign<Nat> for Nat, add_assign);
define_op_0_assign!(impl SubAssign<Nat> for Nat, sub_assign);
define_op_0_assign!(impl MulAssign<Nat> for Nat, mul_assign);
define_op_0_assign!(impl DivAssign<Nat> for Nat, div_assign);
define_op_0_assign!(impl RemAssign<Nat> for Nat, rem_assign);

define_op_0!(impl Add<Int> for Int, add);
define_op_0!(impl Sub<Int> for Int, sub);
define_op_0!(impl Mul<Int> for Int, mul);
define_op_0!(impl Div<Int> for Int, div);
define_op_0!(impl Rem<Int> for Int, rem);

define_op_0_assign!(impl AddAssign<Int> for Int, add_assign);
define_op_0_assign!(impl SubAssign<Int> for Int, sub_assign);
define_op_0_assign!(impl MulAssign<Int> for Int, mul_assign);
define_op_0_assign!(impl DivAssign<Int> for Int, div_assign);
define_op_0_assign!(impl RemAssign<Int> for Int, rem_assign);

// Special cases for literals which are i32, for Nat which isn't support in BigUint,
// so we add a conversion to u32.
impl From<i32> for Nat {
    #[inline]
    fn from(v: i32) -> Self {
        Self::from(v as u32)
    }
}
impl PartialEq<i32> for Nat {
    #[inline]
    #[must_use]
    fn eq(&self, v: &i32) -> bool {
        self.0.eq(&(*v as u32).into())
    }
}

impl std::ops::Add<i32> for Nat {
    type Output = Self;

    #[inline]
    fn add(self, other: i32) -> Self {
        (self.0 + (other as u32)).into()
    }
}
impl std::ops::AddAssign<i32> for Nat {
    #[inline]
    fn add_assign(&mut self, other: i32) {
        self.0 += other as u32
    }
}

impl std::ops::Sub<i32> for Nat {
    type Output = Self;

    #[inline]
    fn sub(self, other: i32) -> Self {
        (self.0 - (other as u32)).into()
    }
}
impl std::ops::SubAssign<i32> for Nat {
    #[inline]
    fn sub_assign(&mut self, other: i32) {
        self.0 -= other as u32
    }
}

impl std::ops::Mul<i32> for Nat {
    type Output = Self;

    #[inline]
    fn mul(self, other: i32) -> Self {
        (self.0 * (other as u32)).into()
    }
}
impl std::ops::MulAssign<i32> for Nat {
    #[inline]
    fn mul_assign(&mut self, other: i32) {
        self.0 *= other as u32
    }
}

impl std::ops::Div<i32> for Nat {
    type Output = Self;

    #[inline]
    fn div(self, other: i32) -> Self {
        (self.0 / (other as u32)).into()
    }
}
impl std::ops::DivAssign<i32> for Nat {
    #[inline]
    fn div_assign(&mut self, other: i32) {
        self.0 /= other as u32
    }
}

impl std::ops::Rem<i32> for Nat {
    type Output = Self;

    #[inline]
    fn rem(self, other: i32) -> Self {
        (self.0 % (other as u32)).into()
    }
}
impl std::ops::RemAssign<i32> for Nat {
    #[inline]
    fn rem_assign(&mut self, other: i32) {
        self.0 %= other as u32
    }
}
