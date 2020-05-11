//! # Candid
//!
//! Candid is an interface description language (IDL) for interacting with _canisters_ (also known as _services_ or _actors_) running on the Internet Computer.
//!
//! There are three common ways that you might find yourself needing to work with Candid in Rust.
//! - As a typed Rust data strcuture. When you write canisters in Rust, you want to have a seamless way of converting data between Rust and Candid.
//! - As an untyped Candid value. When you write generic tools for the Internet Computer without knowing the type of the Candid data.
//! - As text data. When you get the data from CLI or read from a file, you can use the provided parser to send/receive messages.
//!
//! Candid provides efficient, flexible and safe ways of converting data between each of these representations.
//!
//! ## Operating on native Rust values
//! We are using a builder pattern to encode/decode Candid messages.
//! ```
//! fn builder_example() -> Result<(), candid::Error> {
//!   // Serialize 10 numbers to Candid binary format
//!   let mut ser = candid::ser::IDLBuilder::new();
//!   for i in 0..10 {
//!     ser.arg(&i)?;
//!   }
//!   let bytes: Vec<u8> = ser.serialize_to_vec()?;
//!
//!   // Deserialize Candid message and verify the values match
//!   let mut de = candid::de::IDLDeserialize::new(&bytes)?;
//!   let mut i = 0;
//!   while !de.is_done() {
//!     let x = de.get_value::<i32>()?;
//!     assert_eq!(x, i);
//!     i += 1;
//!   }
//!   de.done()?;
//!   Ok(())
//! }
//! # builder_example().unwrap();
//! ```
//!
//! We also provide macros for encoding/decoding Candid message in a convenient way.
//!
//! ```
//! use candid::{Encode, Decode, Result};
//! fn macro_example() -> Result<()> {
//!   let bytes: Vec<u8> = Encode!(&[(42, "text")], &(42, "text"))?;
//!   let (a, b) = Decode!(&bytes, Vec<(i64, &str)>, (i32, String))?;
//!   assert_eq!(a, [(42, "text")]);
//!   assert_eq!(b, (42i32, "text".to_string()));
//!   Ok(())
//! }
//! # macro_example().unwrap();
//! ```
//! `Encode!` macro takes a sequence of Rust values, and returns a binary format `Vec<u8>` that can be sent over the wire.
//! `Decode!` macro takes the binary message and a sequence of Rust types that you want to decode into, and returns a tuple
//! of Rust values of the given types.
//!
//! Note that a fixed Candid message may be decoded to multiple Rust types. For example,
//! we can decode a Candid `text` type into either `String` or `&str` in Rust.
//!
//! ## Operating on user defined struct/enum
//!
//! ```
//! # #[macro_use] extern crate candid;
//! #[derive(CandidType, Deserialize)]
//! struct List {
//!     head: i32,
//!     tail: Option<Box<List>>,
//! }
//! let list = List { head: 42, tail: None };
//!
//! let bytes = Encode!(&list).unwrap();
//! let res = Decode!(&bytes, List);
//! ```
//!
//! ## Operating on untyped Candid values
//! Any valid Candid message can be manipulated a recursive enum representation `candid::parser::value::IDLValue`.
//! Use `ser.value_arg(v)` and `de.get_value::<IDLValue>()` for encoding and decoding the message.
//!
//! ```
//! use candid::{Result, parser::value::IDLValue};
//! fn untyped_examples() -> Result<()> {
//!   let bytes = candid::ser::IDLBuilder::new()
//!     .arg(&Some(42))?
//!     .value_arg(&IDLValue::Int(42))?
//!     .serialize_to_vec()?;
//!
//!   let mut de = candid::de::IDLDeserialize::new(&bytes)?;
//!   let x = de.get_value::<IDLValue>()?;
//!   let y = de.get_value::<i32>()?;
//!   assert_eq!(x, IDLValue::Opt(Box::new(IDLValue::Int(42))));
//!   assert_eq!(y, 42);
//!   de.done()?;
//!   Ok(())
//! }
//! # untyped_examples().unwrap();
//! ```
//!
//! We provide `candid::IDLArgs` to represent a vector of `IDLValue`s,
//! and use `to_bytes()` and `from_bytes()` to encode and decode Candid messages.
//! We also provide a parser to parse Candid value in text format.
//!
//! ```
//! use candid::{IDLArgs, Result};
//! fn untyped_examples() -> Result<()> {
//!   let text_value = r#"
//!      (42, opt true, vec {1;2;3},
//!       opt record {label="text"; 42="haha"})
//!   "#;
//!   let args: IDLArgs = text_value.parse()?;
//!   let encoded: Vec<u8> = args.to_bytes()?;
//!   let decoded: IDLArgs = IDLArgs::from_bytes(&encoded)?;
//!   assert_eq!(args, decoded);
//!   let output: String = decoded.to_string();
//!   let parsed_args: IDLArgs = output.parse()?;
//!   assert_eq!(args, parsed_args);
//!   Ok(())
//! }
//! # untyped_examples().unwrap();
//! ```
//!
//! ## Operating on Candid types
//!
//! ```
//! use candid::{IDLProg, Result, parser::types::to_pretty};
//! fn parser_examples() -> Result<()> {
//!   let did_file = r#"
//!     type List = record { head: int; tail: List };
//!     service : {
//!       f : (x: blob, opt bool) -> (variant { A; B; C });
//!       g : (List) -> (int) query;
//!     }
//!   "#;
//!   let ast: IDLProg = did_file.parse()?;
//!   let pretty: String = to_pretty(&ast, 80);
//!   let showList = to_pretty(&ast.find_type("List")?, 80);
//!   let showMethod = to_pretty(&ast.get_method_type("g").unwrap(), 80);
//!   Ok(())
//! }
//! # parser_examples().unwrap();
//! ```
//!

extern crate leb128;
extern crate num_enum;
extern crate serde;

extern crate candid_derive;
pub use candid_derive::CandidType;
pub use serde::Deserialize;

pub mod types;
pub use types::CandidType;

pub mod error;
pub use error::{Error, Result};

pub mod parser;
pub use parser::types::IDLProg;
pub use parser::value::IDLArgs;

pub mod de;
pub mod ser;

// Candid hash function comes from
// https://caml.inria.fr/pub/papers/garrigue-polymorphic_variants-ml98.pdf
// Not public API. Only used by tests.
#[doc(hidden)]
#[inline]
pub fn idl_hash(id: &str) -> u32 {
    let mut s: u32 = 0;
    for c in id.chars() {
        s = s.wrapping_mul(223).wrapping_add(c as u32);
    }
    s
}

/// Encode sequence of Rust values into Candid message in a Result type.
#[macro_export]
macro_rules! Encode {
    ( $($x:expr),* ) => {{
        let mut builder = candid::ser::IDLBuilder::new();
        Encode!(@PutValue builder $($x,)*)
    }};
    ( @PutValue $builder:ident $x:expr, $($tail:expr,)* ) => {{
        $builder.arg($x).and_then(|mut builder| Encode!(@PutValue builder $($tail,)*))
    }};
    ( @PutValue $builder:ident ) => {{
        $builder.serialize_to_vec()
    }};
}

/// Decode Candid message into an tuple of Rust values of the given types.
/// Produces `Err` if the message fails to decode at any given types.
/// If the message contains only one value, it returns the value directly instead of a tuple.
#[macro_export]
macro_rules! Decode {
    ( $hex:expr $(,$ty:ty)* ) => {{
        candid::de::IDLDeserialize::new($hex)
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
