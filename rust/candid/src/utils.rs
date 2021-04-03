use crate::de::IDLDeserialize;
use crate::{CandidType, Result};
use serde::de::Deserialize;

/// Decode a series of arguments, represented as a tuple. There is a maximum of 16 arguments
/// supported.
///
/// Example:
///
/// ```
/// # use candid::Encode;
/// # use candid::de::decode_args;
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
/// # use candid::de::decode_one;
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
