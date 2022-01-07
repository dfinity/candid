use crate::de::IDLDeserialize;
use crate::ser::IDLBuilder;
use crate::{check_prog, pretty_check_file, pretty_parse, types::Type, TypeEnv};
use crate::{CandidType, Error, Result};
use serde::de::Deserialize;
use std::path::Path;

pub enum CandidSource<'a> {
    File(&'a Path),
    Text(&'a str),
}
impl<'a> CandidSource<'a> {
    pub fn load(&self) -> Result<(TypeEnv, Option<Type>)> {
        Ok(match self {
            CandidSource::File(path) => pretty_check_file(path)?,
            CandidSource::Text(str) => {
                let ast = pretty_parse("", str)?;
                let mut env = TypeEnv::new();
                let actor = check_prog(&mut env, &ast)?;
                (env, actor)
            }
        })
    }
}

/// Check compatibility of two service types
pub fn service_compatible(new: CandidSource, old: CandidSource) -> Result<()> {
    let (mut env, t1) = new.load()?;
    let t1 = t1.ok_or_else(|| Error::msg("new interface has no main service type"))?;
    let (env2, t2) = old.load()?;
    let t2 = t2.ok_or_else(|| Error::msg("old interface has no main service type"))?;
    let mut gamma = std::collections::HashSet::new();
    let t2 = env.merge_type(env2, t2);
    crate::types::subtype::subtype(&mut gamma, &env, &t1, &t2)?;
    Ok(())
}

/// Encode sequence of Rust values into Candid message of type `candid::Result<Vec<u8>>`.
#[macro_export]
macro_rules! Encode {
    ( $($x:expr),* ) => {{
        let mut builder = $crate::ser::IDLBuilder::new();
        Encode!(@PutValue builder $($x,)*)
    }};
    ( @PutValue $builder:ident $x:expr, $($tail:expr,)* ) => {{
        $builder.arg($x).and_then(|builder| Encode!(@PutValue builder $($tail,)*))
    }};
    ( @PutValue $builder:ident ) => {{
        $builder.serialize_to_vec()
    }};
}

/// Decode Candid message into a tuple of Rust values of the given types.
/// Produces `Err` if the message fails to decode at any given types.
/// If the message contains only one value, it returns the value directly instead of a tuple.
#[macro_export]
macro_rules! Decode {
    ( $hex:expr $(,$ty:ty)* ) => {{
        $crate::de::IDLDeserialize::new($hex)
            .and_then(|mut de| Decode!(@GetValue [] de $($ty,)*)
                      .and_then(|res| de.done().and(Ok(res))))
    }};
    (@GetValue [$($ans:ident)*] $de:ident $ty:ty, $($tail:ty,)* ) => {{
        $de.get_value::<$ty>()
            .and_then(|val| Decode!(@GetValue [$($ans)* val] $de $($tail,)* ))
    }};
    (@GetValue [$($ans:ident)*] $de:ident) => {{
        Ok(($($ans),*))
    }};
}

/// Decode a series of arguments, represented as a tuple. There is a maximum of 16 arguments
/// supported.
///
/// Example:
///
/// ```
/// # use candid::Encode;
/// # use candid::decode_args;
/// let golden1 = 123u64;
/// let golden2 = "456";
/// let bytes = Encode!(&golden1, &golden2).unwrap();
/// let (value1, value2): (u64, String) = decode_args(&bytes).unwrap();
///
/// assert_eq!(golden1, value1);
/// assert_eq!(golden2, value2);
/// ```
pub fn decode_args<'a, Tuple>(bytes: &'a [u8]) -> Result<Tuple>
where
    Tuple: ArgumentDecoder<'a>,
{
    let mut de = IDLDeserialize::new(bytes)?;
    let res = ArgumentDecoder::decode(&mut de)?;
    de.done()?;
    Ok(res)
}

/// Decode a single argument.
///
/// Example:
///
/// ```
/// # use candid::Encode;
/// # use candid::decode_one;
/// let golden1 = 123u64;
/// let bytes = Encode!(&golden1).unwrap();
/// let value1: u64 = decode_one(&bytes).unwrap();
///
/// assert_eq!(golden1, value1);
/// ```
pub fn decode_one<'a, T>(bytes: &'a [u8]) -> Result<T>
where
    T: Deserialize<'a> + CandidType,
{
    let (res,) = decode_args(bytes)?;
    Ok(res)
}

/// Serialize an encoding of a tuple and write it to a `Write` buffer.
///
/// ```
/// # use candid::Decode;
/// # use candid::write_args;
/// let golden1 = 1u64;
/// let golden2 = "hello";
/// let mut buffer = Vec::new();
/// write_args(&mut buffer, (golden1, golden2)).unwrap();
///
/// let (value1, value2) = Decode!(&buffer, u64, String).unwrap();
/// assert_eq!(golden1, value1);
/// assert_eq!(golden2, value2);
/// ```
pub fn write_args<Tuple: ArgumentEncoder, Writer: std::io::Write>(
    writer: &mut Writer,
    arguments: Tuple,
) -> Result<()> {
    let mut ser = IDLBuilder::new();
    arguments.encode(&mut ser)?;
    ser.serialize(writer)
}

/// Serialize an encoding of a tuple to a vector of bytes.
///
/// ```
/// # use candid::Decode;
/// # use candid::encode_args;
/// let golden1 = 1u64;
/// let golden2 = "hello";
/// let buffer = encode_args((golden1, golden2)).unwrap();
///
/// let (value1, value2) = Decode!(&buffer, u64, String).unwrap();
/// assert_eq!(golden1, value1);
/// assert_eq!(golden2, value2);
/// ```
pub fn encode_args<Tuple: ArgumentEncoder>(arguments: Tuple) -> Result<Vec<u8>> {
    let mut result = Vec::new();
    write_args(&mut result, arguments)?;
    Ok(result)
}

/// Serialize a single value to a vector of bytes.
///
/// ```
/// # use candid::Decode;
/// # use candid::encode_one;
/// let golden = "hello";
/// let buffer = encode_one(golden).unwrap();
///
/// let (value) = Decode!(&buffer, String).unwrap();
/// assert_eq!(golden, value);
/// ```
pub fn encode_one<T: CandidType>(argument: T) -> Result<Vec<u8>> {
    encode_args((argument,))
}

/// Allow decoding of any sized argument.
pub trait ArgumentDecoder<'a>: Sized {
    /// Decodes a value of type [Self], modifying the deserializer (values are consumed).
    fn decode(de: &mut IDLDeserialize<'a>) -> Result<Self>;
}

/// Decode an empty tuple.
impl<'a> ArgumentDecoder<'a> for () {
    fn decode(_de: &mut IDLDeserialize<'a>) -> Result<()> {
        Ok(())
    }
}

/// Allow encoding of any serializable value.
pub trait ArgumentEncoder {
    /// Encode a value of type [Self].
    fn encode(self, ser: &mut IDLBuilder) -> Result<()>;
}

/// Decode an empty tuple.
impl ArgumentEncoder for () {
    fn encode(self, _de: &mut IDLBuilder) -> Result<()> {
        Ok(())
    }
}

// Create implementation of [ArgumentDecoder] for up to 16 value tuples.
macro_rules! decode_impl {
    ( $($id: ident : $typename: ident),* ) => {
        impl<'a, $( $typename ),*> ArgumentDecoder<'a> for ($($typename,)*)
        where
            $( $typename: Deserialize<'a> + CandidType ),*
        {
            fn decode(de: &mut IDLDeserialize<'a>) -> Result<Self> {
                $(
                let $id: $typename = de.get_value()?;
                )*

                Ok(($( $id, )*))
            }
        }
    }
}

// Create implementation of [ArgumentEncoder] for up to 16 value tuples.
macro_rules! encode_impl {
    ( $($id: ident : $typename: ident),* ) => {
        impl<$( $typename ),*> ArgumentEncoder for ($($typename,)*)
        where
            $( $typename: CandidType ),*
        {
            fn encode(self, ser: &mut IDLBuilder) -> Result<()> {
                let ( $( $id, )* ) = self;
                $(
                ser.arg(&$id)?;
                )*

                Ok(())
            }
        }
    }
}

decode_impl!(a: A);
decode_impl!(a: A, b: B);
decode_impl!(a: A, b: B, c: C);
decode_impl!(a: A, b: B, c: C, d: D);
decode_impl!(a: A, b: B, c: C, d: D, e: E);
decode_impl!(a: A, b: B, c: C, d: D, e: E, f: F);
decode_impl!(a: A, b: B, c: C, d: D, e: E, f: F, g: G);
decode_impl!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H);
decode_impl!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I);
decode_impl!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J);
#[rustfmt::skip]
decode_impl!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K);
#[rustfmt::skip]
decode_impl!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L);
#[rustfmt::skip]
decode_impl!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M);
#[rustfmt::skip]
decode_impl!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N);
#[rustfmt::skip]
decode_impl!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O);
#[rustfmt::skip]
decode_impl!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P);

encode_impl!(a: A);
encode_impl!(a: A, b: B);
encode_impl!(a: A, b: B, c: C);
encode_impl!(a: A, b: B, c: C, d: D);
encode_impl!(a: A, b: B, c: C, d: D, e: E);
encode_impl!(a: A, b: B, c: C, d: D, e: E, f: F);
encode_impl!(a: A, b: B, c: C, d: D, e: E, f: F, g: G);
encode_impl!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H);
encode_impl!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I);
encode_impl!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J);
#[rustfmt::skip]
encode_impl!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K);
#[rustfmt::skip]
encode_impl!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L);
#[rustfmt::skip]
encode_impl!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M);
#[rustfmt::skip]
encode_impl!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N);
#[rustfmt::skip]
encode_impl!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O);
#[rustfmt::skip]
encode_impl!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P);
