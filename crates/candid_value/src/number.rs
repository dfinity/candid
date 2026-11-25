//! `nat` and `int`: integers of any size.
//!
//! They wrap `num-bigint` without exposing it, so the API is this module's: conversion to
//! and from Rust's integers, decimal text, comparison, arithmetic, and the number's bytes.
//! The bytes are a fact about integers, not about the storage, so they are the way out to
//! any other big-number crate; `num-bigint` 0.4 also has `From` and `Into` behind the
//! `num-bigint-04` feature.

use core::fmt;
use core::ops::{
    Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign,
};
use core::str::FromStr;

use num_bigint::{BigInt, BigUint, Sign};
use num_traits::{CheckedSub, ToPrimitive, Zero};

/// A `nat`: a natural number of any size.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Nat(BigUint);

/// An `int`: an integer of any size.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Int(BigInt);

impl Nat {
    /// The number whose base-256 digits `bytes` are, least significant first. Any length:
    /// trailing zero bytes add nothing, and no bytes is 0.
    pub fn from_le_bytes(bytes: &[u8]) -> Nat {
        Nat(BigUint::from_bytes_le(bytes))
    }

    /// The number's base-256 digits, least significant first, in as few bytes as there
    /// are: no trailing zero byte, so 0 is no bytes.
    pub fn to_le_bytes(&self) -> Vec<u8> {
        if self.0.is_zero() {
            Vec::new()
        } else {
            self.0.to_bytes_le()
        }
    }

    /// `self - other`, or `None` if that is negative.
    pub fn checked_sub(&self, other: &Nat) -> Option<Nat> {
        self.0.checked_sub(&other.0).map(Nat)
    }
}

impl Int {
    /// The number `bytes` are in two's complement, least significant byte first. Any
    /// length: the top bit of the last byte is the sign, trailing bytes that repeat it add
    /// nothing, and no bytes is 0.
    pub fn from_le_bytes(bytes: &[u8]) -> Int {
        Int(BigInt::from_signed_bytes_le(bytes))
    }

    /// The number in two's complement, least significant byte first, in as few bytes as
    /// hold it with its sign, so 0 is no bytes.
    pub fn to_le_bytes(&self) -> Vec<u8> {
        if self.0.is_zero() {
            Vec::new()
        } else {
            self.0.to_signed_bytes_le()
        }
    }

    /// The magnitude, which is a `nat`.
    pub fn magnitude(&self) -> Nat {
        Nat(self.0.magnitude().clone())
    }

    /// Whether it is below 0.
    pub fn is_negative(&self) -> bool {
        self.0.sign() == Sign::Minus
    }
}

impl From<Nat> for Int {
    fn from(n: Nat) -> Int {
        Int(BigInt::from(n.0))
    }
}

impl TryFrom<Int> for Nat {
    type Error = OutOfRange;

    fn try_from(i: Int) -> Result<Nat, OutOfRange> {
        i.0.to_biguint().map(Nat).ok_or(OutOfRange)
    }
}

impl TryFrom<&Int> for Nat {
    type Error = OutOfRange;

    fn try_from(i: &Int) -> Result<Nat, OutOfRange> {
        i.0.to_biguint().map(Nat).ok_or(OutOfRange)
    }
}

/// A conversion of an integer to one it does not fit in.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct OutOfRange;

impl fmt::Display for OutOfRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("the number is out of range")
    }
}

impl core::error::Error for OutOfRange {}

/// Text that is not a number in decimal.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ParseNumberError;

impl fmt::Display for ParseNumberError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("not a number in decimal")
    }
}

impl core::error::Error for ParseNumberError {}

/// Decimal digits, and for an `Int` a `-` before them: nothing else, not even `+` or `_`,
/// which `num-bigint` would accept.
fn decimal(s: &str, signed: bool) -> Result<&str, ParseNumberError> {
    let digits = if signed {
        s.strip_prefix('-').unwrap_or(s)
    } else {
        s
    };
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return Err(ParseNumberError);
    }
    Ok(s)
}

impl FromStr for Nat {
    type Err = ParseNumberError;

    /// Decimal digits.
    fn from_str(s: &str) -> Result<Nat, ParseNumberError> {
        BigUint::from_str(decimal(s, false)?)
            .map(Nat)
            .map_err(|_| ParseNumberError)
    }
}

impl FromStr for Int {
    type Err = ParseNumberError;

    /// Decimal digits, after a `-` if negative.
    fn from_str(s: &str) -> Result<Int, ParseNumberError> {
        BigInt::from_str(decimal(s, true)?)
            .map(Int)
            .map_err(|_| ParseNumberError)
    }
}

macro_rules! text {
    ($($t:ident),*) => {$(
        /// In decimal.
        impl fmt::Display for $t {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Display::fmt(&self.0, f)
            }
        }

        /// In decimal, as [`Display`](fmt::Display).
        impl fmt::Debug for $t {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Display::fmt(&self.0, f)
            }
        }
    )*};
}
text!(Nat, Int);

/// To and from Rust's integers: `From` the ones that always fit, `TryFrom` back.
macro_rules! fixed {
    ($t:ident, $to:ident: $($n:ty),*) => {$(
        impl From<$n> for $t {
            fn from(n: $n) -> $t {
                $t(n.into())
            }
        }

        impl TryFrom<&$t> for $n {
            type Error = OutOfRange;

            fn try_from(n: &$t) -> Result<$n, OutOfRange> {
                n.0.$to().ok_or(OutOfRange)
            }
        }

        impl TryFrom<$t> for $n {
            type Error = OutOfRange;

            fn try_from(n: $t) -> Result<$n, OutOfRange> {
                <$n>::try_from(&n)
            }
        }
    )*};
}

macro_rules! fixed_all {
    ($t:ident: $($n:ty => $to:ident),*) => {$( fixed!($t, $to: $n); )*};
}

fixed_all!(Nat: u8 => to_u8, u16 => to_u16, u32 => to_u32, u64 => to_u64, u128 => to_u128,
    usize => to_usize);
fixed_all!(Int: u8 => to_u8, u16 => to_u16, u32 => to_u32, u64 => to_u64, u128 => to_u128,
    usize => to_usize, i8 => to_i8, i16 => to_i16, i32 => to_i32, i64 => to_i64,
    i128 => to_i128, isize => to_isize);

/// An operator on owned and borrowed operands, and its assigning form.
macro_rules! arithmetic {
    ($t:ident: $($op:ident $f:ident $assign:ident $fa:ident),*) => {$(
        impl $op<$t> for $t {
            type Output = $t;
            fn $f(self, other: $t) -> $t {
                $t(self.0.$f(other.0))
            }
        }

        impl $op<&$t> for $t {
            type Output = $t;
            fn $f(self, other: &$t) -> $t {
                $t(self.0.$f(&other.0))
            }
        }

        impl $op<$t> for &$t {
            type Output = $t;
            fn $f(self, other: $t) -> $t {
                $t((&self.0).$f(other.0))
            }
        }

        impl $op<&$t> for &$t {
            type Output = $t;
            fn $f(self, other: &$t) -> $t {
                $t((&self.0).$f(&other.0))
            }
        }

        impl $assign<$t> for $t {
            fn $fa(&mut self, other: $t) {
                self.0.$fa(other.0);
            }
        }

        impl $assign<&$t> for $t {
            fn $fa(&mut self, other: &$t) {
                self.0.$fa(&other.0);
            }
        }
    )*};
}

// `Nat`'s subtraction panics below zero, as an unsigned integer's does in a debug build;
// `Nat::checked_sub` does not. Division and remainder panic at zero, as Rust's do.
arithmetic!(Nat: Add add AddAssign add_assign, Sub sub SubAssign sub_assign,
    Mul mul MulAssign mul_assign, Div div DivAssign div_assign, Rem rem RemAssign rem_assign);
arithmetic!(Int: Add add AddAssign add_assign, Sub sub SubAssign sub_assign,
    Mul mul MulAssign mul_assign, Div div DivAssign div_assign, Rem rem RemAssign rem_assign);

impl Neg for Int {
    type Output = Int;
    fn neg(self) -> Int {
        Int(-self.0)
    }
}

impl Neg for &Int {
    type Output = Int;
    fn neg(self) -> Int {
        Int(-&self.0)
    }
}

#[cfg(feature = "num-bigint-04")]
mod num_bigint_04 {
    use super::{Int, Nat};
    use num_bigint::{BigInt, BigUint};

    impl From<BigUint> for Nat {
        fn from(n: BigUint) -> Nat {
            Nat(n)
        }
    }

    impl From<Nat> for BigUint {
        fn from(n: Nat) -> BigUint {
            n.0
        }
    }

    impl From<BigInt> for Int {
        fn from(i: BigInt) -> Int {
            Int(i)
        }
    }

    impl From<Int> for BigInt {
        fn from(i: Int) -> BigInt {
            i.0
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bytes() {
        assert_eq!(Nat::from(0u8).to_le_bytes(), Vec::<u8>::new());
        assert_eq!(Nat::from(300u16).to_le_bytes(), [0x2c, 0x01]);
        assert_eq!(Nat::from_le_bytes(&[0x2c, 0x01, 0, 0]), Nat::from(300u16));
        assert_eq!(Nat::from_le_bytes(&[]), Nat::default());
        assert_eq!(Int::from(-129).to_le_bytes(), [0x7f, 0xff]);
        assert_eq!(Int::from(128).to_le_bytes(), [0x80, 0x00]);
        assert_eq!(Int::from(-1).to_le_bytes(), [0xff]);
        assert_eq!(Int::from(0).to_le_bytes(), Vec::<u8>::new());
        assert_eq!(Int::from_le_bytes(&[0x7f, 0xff, 0xff]), Int::from(-129));
        for i in [i128::MIN, -1, 0, 1, i128::MAX] {
            let n = Int::from(i);
            assert_eq!(Int::from_le_bytes(&n.to_le_bytes()), n);
            assert_eq!(i128::try_from(&n), Ok(i));
        }
    }

    #[test]
    fn decimal_text() {
        let big = "340282366920938463463374607431768211456"; // 2^128
        assert_eq!(big.parse::<Nat>().unwrap().to_string(), big);
        assert_eq!("-5".parse::<Int>(), Ok(Int::from(-5)));
        for bad in ["", "-", "+5", "1_000", " 1", "0x10"] {
            assert_eq!(bad.parse::<Int>(), Err(ParseNumberError), "{bad:?}");
        }
        assert_eq!("-5".parse::<Nat>(), Err(ParseNumberError));
    }

    #[test]
    fn conversions_and_arithmetic() {
        let max = Nat::from(u64::MAX);
        assert_eq!(u64::try_from(&max), Ok(u64::MAX));
        let past = &max + Nat::from(1u8);
        assert_eq!(u64::try_from(&past), Err(OutOfRange));
        assert_eq!(past.checked_sub(&max), Some(Nat::from(1u8)));
        assert_eq!(max.checked_sub(&past), None);
        assert_eq!(Nat::try_from(Int::from(-1)), Err(OutOfRange));
        assert_eq!(-Int::from(past.clone()) + Int::from(past), Int::default());
        assert!(Int::from(-3).is_negative());
        assert_eq!(Int::from(-3).magnitude(), Nat::from(3u8));
        assert!(Nat::from(2u8) < Nat::from(10u8));
    }
}
