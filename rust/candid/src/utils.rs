use crate::de::{DecoderConfig, IDLDeserialize};
use crate::ser::IDLBuilder;
use crate::{CandidType, Error, Result};
use serde::de::Deserialize;

pub fn check_unique<'a, I, T>(sorted: I) -> Result<()>
where
    T: 'a + PartialEq + std::fmt::Display,
    I: Iterator<Item = &'a T>,
{
    let mut prev: Option<&T> = None;
    for lab in sorted {
        if let Some(prev) = prev {
            if lab == prev {
                return Err(Error::msg(format!(
                    "label '{lab}' hash collision with '{prev}'"
                )));
            }
        }
        prev = Some(lab);
    }
    Ok(())
}

pub fn pp_num_str(s: &str) -> String {
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
/// ```
/// use candid::{Encode, Decode, DecoderConfig};
/// let bytes = Encode!(&42u32, &"hello", &"extra arguments")?;
/// let (value1, value2) = Decode!(&bytes, u32, String)?;
/// assert_eq!(value1, 42);
/// assert_eq!(value2, "hello");
///
/// // Decode with quota
/// let mut config = DecoderConfig::new();
/// config.set_decoding_quota(1000).set_skipping_quota(50);
/// let (value1, value2) = Decode!([config]; &bytes, u32, String)?;
/// let ((value1, value2), cost) = Decode!(@Debug [config]; &bytes, u32, String)?;
/// // `cost` reports the decoding cost, not the remaining quota
/// assert_eq!(cost.decoding_quota, Some(846));
/// assert_eq!(cost.skipping_quota, Some(16));
/// # Ok::<(), candid::Error>(())
/// ```
#[macro_export]
macro_rules! Decode {
    ( $hex:expr $(,$ty:ty)* ) => {{
        Decode!([$crate::de::DecoderConfig::new()]; $hex $(,$ty)*)
    }};
    ( [ $config:expr ] ; $hex:expr $(,$ty:ty)* ) => {{
        $crate::de::IDLDeserialize::new_with_config($hex, &$config)
            .and_then(|mut de| Decode!(@GetValue [] de $($ty,)*)
                      .and_then(|res| de.done().and(Ok(res))))
    }};
    (@Debug [ $config:expr ] ; $hex:expr $(,$ty:ty)* ) => {{
        $crate::de::IDLDeserialize::new_with_config($hex, &$config)
            .and_then(|mut de| Decode!(@GetValue [] de $($ty,)*)
                      .and_then(|res| de.done().and(Ok((res, de.get_config().compute_cost(&$config))))))
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
pub fn decode_args_with_config<'a, Tuple>(bytes: &'a [u8], config: &DecoderConfig) -> Result<Tuple>
where
    Tuple: ArgumentDecoder<'a>,
{
    let mut de = IDLDeserialize::new_with_config(bytes, config)?;
    let res = ArgumentDecoder::decode(&mut de)?;
    de.done()?;
    Ok(res)
}
pub fn decode_args_with_config_debug<'a, Tuple>(
    bytes: &'a [u8],
    config: &DecoderConfig,
) -> Result<(Tuple, DecoderConfig)>
where
    Tuple: ArgumentDecoder<'a>,
{
    let mut de = IDLDeserialize::new_with_config(bytes, config)?;
    let res = ArgumentDecoder::decode(&mut de)?;
    de.done()?;
    let cost = de.get_config().compute_cost(config);
    Ok((res, cost))
}

/// Decode a series of arguments, represented as a tuple, with a decoding_quota specified as a const generic number.
///
/// This function is particularly useful as a decoder in ic-cdk macros (version 0.18 and up).
///
/// Example:
///
/// ```ignore
/// #[ic_cdk::query(decode_with = "decode_args_with_decoding_quota::<10000,_>")]
/// fn count(arg1: String, arg2: String) -> u32 {
///    arg1.len() as u32 + arg2.len() as u32
/// }
/// ```
pub fn decode_args_with_decoding_quota<const N: usize, Tuple>(byte_vec: Vec<u8>) -> Tuple
where
    Tuple: for<'a> ArgumentDecoder<'a>,
{
    let mut config = DecoderConfig::new();
    config.set_decoding_quota(N);
    decode_args_with_config(&byte_vec[..], &config).unwrap()
}

/// Decode a series of arguments, represented as a tuple, with a skipping_quota specified as a const generic number.
///
/// This function is particularly useful as a decoder in ic-cdk macros (version 0.18 and up).
///
/// Example:
///
/// ```ignore
/// #[ic_cdk::query(decode_with = "decode_args_with_skipping_quota::<10000,_>")]
/// fn count(arg1: String, arg2: String) -> u32 {
///    arg1.len() as u32 + arg2.len() as u32
/// }
/// ```
pub fn decode_args_with_skipping_quota<const M: usize, Tuple>(byte_vec: Vec<u8>) -> Tuple
where
    Tuple: for<'a> ArgumentDecoder<'a>,
{
    let mut config = DecoderConfig::new();
    config.set_skipping_quota(M);
    decode_args_with_config(&byte_vec[..], &config).unwrap()
}

/// Decode a series of arguments, represented as a tuple, with decoding_quota and skipping_quota specified as const generic numbers.
///
/// This function is particularly useful as a decoder in ic-cdk macros (version 0.18 and up).
///
/// Example:
///
/// ```ignore
/// #[ic_cdk::query(decode_with = "decode_args_with_decoding_and_skipping_quota::<10000,10000,_>")]
/// fn count(arg1: String, arg2: String) -> u32 {
///    arg1.len() as u32 + arg2.len() as u32
/// }
/// ```
pub fn decode_args_with_decoding_and_skipping_quota<const N: usize, const M: usize, Tuple>(
    byte_vec: Vec<u8>,
) -> Tuple
where
    Tuple: for<'a> ArgumentDecoder<'a>,
{
    let mut config = DecoderConfig::new();
    config.set_decoding_quota(N);
    config.set_skipping_quota(M);
    decode_args_with_config(&byte_vec[..], &config).unwrap()
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
pub fn decode_one_with_config<'a, T>(bytes: &'a [u8], config: &DecoderConfig) -> Result<T>
where
    T: Deserialize<'a> + CandidType,
{
    let (res,) = decode_args_with_config(bytes, config)?;
    Ok(res)
}

/// Decode a single argument with a decoding_quota specified as a const generic number.
///
/// This function is particularly useful as a decoder in ic-cdk macros (version 0.18 and up).
///
/// Example:
///
/// ```ignore
/// #[ic_cdk::query(decode_with = "decode_one_with_decoding_quota::<10000,_>")]
/// fn count(arg: String) -> u32 {
///    arg.len() as u32
/// }
/// ```
pub fn decode_one_with_decoding_quota<const N: usize, T>(byte_vec: Vec<u8>) -> T
where
    T: for<'a> Deserialize<'a> + CandidType,
{
    let mut config = DecoderConfig::new();
    config.set_decoding_quota(N);
    decode_one_with_config(&byte_vec[..], &config).unwrap()
}

/// Decode a single argument with a skipping_quota specified as a const generic number.
///
/// This function is particularly useful as a decoder in ic-cdk macros (version 0.18 and up).
///
/// Example:
///
/// ```ignore
/// #[ic_cdk::query(decode_with = "decode_one_with_skipping_quota::<10000,_>")]
/// fn count(arg: String) -> u32 {
///    arg.len() as u32
/// }
/// ```
pub fn decode_one_with_skipping_quota<const M: usize, T>(byte_vec: Vec<u8>) -> T
where
    T: for<'a> Deserialize<'a> + CandidType,
{
    let mut config = DecoderConfig::new();
    config.set_skipping_quota(M);
    decode_one_with_config(&byte_vec[..], &config).unwrap()
}

/// Decode a single argument with decoding_quota and skipping_quota specified as const generic numbers.
///
/// This function is particularly useful as a decoder in ic-cdk macros (version 0.18 and up).
///
/// Example:
///
/// ```ignore
/// #[ic_cdk::query(decode_with = "decode_one_with_decoding_and_skipping_quota::<10000,10000,_>")]
/// fn count(arg: String) -> u32 {
///    arg.len() as u32
/// }
/// ```
pub fn decode_one_with_decoding_and_skipping_quota<const N: usize, const M: usize, T>(
    byte_vec: Vec<u8>,
) -> T
where
    T: for<'a> Deserialize<'a> + CandidType,
{
    let mut config = DecoderConfig::new();
    config.set_decoding_quota(N);
    config.set_skipping_quota(M);
    decode_one_with_config(&byte_vec[..], &config).unwrap()
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

/// Serialize an encoding of a tuple and write it to a `Write` buffer.
///
/// ```
/// # use candid::Decode;
/// # use candid::utils::write_args_ref;
/// let golden1 = 1u64;
/// let golden2 = "hello";
/// let mut buffer = Vec::new();
/// write_args_ref(&mut buffer, &(golden1, golden2)).unwrap();
///
/// let (value1, value2) = Decode!(&buffer, u64, String).unwrap();
/// assert_eq!(golden1, value1);
/// assert_eq!(golden2, value2);
/// ```
pub fn write_args_ref<Tuple: ArgumentEncoder, Writer: std::io::Write>(
    writer: &mut Writer,
    arguments: &Tuple,
) -> Result<()> {
    let mut ser = IDLBuilder::new();
    arguments.encode_ref(&mut ser)?;
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

/// Serialize an encoding of a tuple to a vector of bytes.
///
/// ```
/// # use candid::Decode;
/// # use candid::utils::encode_args_ref;
/// let golden1 = 1u64;
/// let golden2 = "hello";
/// let buffer = encode_args_ref(&(golden1, golden2)).unwrap();
///
/// let (value1, value2) = Decode!(&buffer, u64, String).unwrap();
/// assert_eq!(golden1, value1);
/// assert_eq!(golden2, value2);
/// ```
pub fn encode_args_ref<Tuple: ArgumentEncoder>(arguments: &Tuple) -> Result<Vec<u8>> {
    let mut result = Vec::new();
    write_args_ref(&mut result, arguments)?;
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

    /// Encode a reference value of type [Self].
    fn encode_ref(&self, ser: &mut IDLBuilder) -> Result<()>;
}

/// Decode an empty tuple.
impl ArgumentEncoder for () {
    fn encode(self, _ser: &mut IDLBuilder) -> Result<()> {
        Ok(())
    }

    fn encode_ref(&self, _ser: &mut IDLBuilder) -> Result<()> {
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

            fn encode_ref(&self, ser: &mut IDLBuilder) -> Result<()> {
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
