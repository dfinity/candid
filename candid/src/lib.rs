//! # Candid
//!
//! Candid is an interface description language (IDL) for interacting with _canisters_ (also known as _services_ or _actors_) running on the Internet Computer.
//!
//! There are three common ways that you might find yourself needing to work with Candid in Rust.
//! - As a typed Rust data strcuture. When you write canisters or frontend in Rust, you want to have a seamless way of converting data between Rust and Candid.
//! - As an untyped Candid value. When you write generic tools for the Internet Computer without knowing the type of the Candid data.
//! - As text data. When you get the data from CLI or read from a file, you can use the provided parser to send/receive messages.
//!
//! Candid provides efficient, flexible and safe ways of converting data between each of these representations.
//!
//! ## Operating on native Rust values
//! We are using a builder pattern to encode/decode Candid messages, see [`candid::ser::IDLBuilder`](ser/struct.IDLBuilder.html) for serialization and [`candid::de::IDLDeserialize`](de/struct.IDLDeserialize.html) for deserialization.
//!
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
//!   // Serialize two values [(42, "text")] and (42u32, "text")
//!   let bytes: Vec<u8> = Encode!(&[(42, "text")], &(42u32, "text"))?;
//!   // Deserialize the first value as type Vec<(i32, &str)>,
//!   // and the second value as type (u32, String)
//!   let (a, b) = Decode!(&bytes, Vec<(i32, &str)>, (u32, String))?;
//!
//!   assert_eq!(a, [(42, "text")]);
//!   assert_eq!(b, (42u32, "text".to_string()));
//!   Ok(())
//! }
//! # macro_example().unwrap();
//! ```
//! The [`Encode!`](macro.Encode.html) macro takes a sequence of Rust values, and returns a binary format `Vec<u8>` that can be sent over the wire.
//! The [`Decode!`](macro.Decode.html) macro takes the binary message and a sequence of Rust types that you want to decode into, and returns a tuple
//! of Rust values of the given types.
//!
//! Note that a fixed Candid message may be decoded in multiple Rust types. For example,
//! we can decode a Candid `text` type into either `String` or `&str` in Rust.
//!
//! ## Operating on user defined struct/enum
//! We use trait [`CandidType`](types/trait.CandidType.html) for serialization, and Serde's [`Deserialize`](trait.Deserialize.html) trait for deserialization.
//! Any type that implements these two traits can be used for serialization and deserialization respectively.
//! This includes built-in Rust standard library types like `Vec<T>` and `Result<T, E>`, as well as any structs
//! or enums annotated with `#[derive(CandidType, Deserialize)]`.
//!
//! We do not use Serde's `Serialize` trait because Candid requires serializing types along with the values.
//! This is difficult to achieve in `Serialize`, especially for enum types. Besides serialization, [`CandidType`](types/trait.CandidType.html)
//! trait also converts Rust type to Candid type defined as [`candid::types::Type`](types/internal/enum.Type.html).
//! ```
//! use candid::{Encode, Decode, CandidType, Deserialize};
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
//! Any valid Candid value can be manipulated in an recursive enum representation [`candid::parser::value::IDLValue`](parser/value/enum.IDLValue.html).
//! We use `ser.value_arg(v)` and `de.get_value::<IDLValue>()` for encoding and decoding the value.
//! The use of Rust value and `IDLValue` can be intermixed.
//!
//! ```
//! use candid::{Result, parser::value::IDLValue};
//! fn untyped_examples() -> Result<()> {
//!   // Serialize Rust value Some(42) and IDLValue "hello"
//!   let bytes = candid::ser::IDLBuilder::new()
//!     .arg(&Some(42))?
//!     .value_arg(&IDLValue::Text("hello".to_string()))?
//!     .serialize_to_vec()?;
//!
//!   // Deserialize the first Rust value into IDLValue,
//!   // and the second IDLValue into Rust value
//!   let mut de = candid::de::IDLDeserialize::new(&bytes)?;
//!   let x = de.get_value::<IDLValue>()?;
//!   let y = de.get_value::<&str>()?;
//!   de.done()?;
//!
//!   assert_eq!(x, IDLValue::Opt(Box::new(IDLValue::Int(42))));
//!   assert_eq!(y, "hello");
//!   Ok(())
//! }
//! # untyped_examples().unwrap();
//! ```
//!
//! We provide a data structure [`candid::IDLArgs`](parser/value/struct.IDLArgs.html) to represent a sequence of `IDLValue`s,
//! and use `to_bytes()` and `from_bytes()` to encode and decode Candid messages.
//! We also provide a parser to parse Candid values in text format.
//!
//! ```
//! use candid::{IDLArgs, Result};
//! fn untyped_examples() -> Result<()> {
//!   // Candid values represented in text format
//!   let text_value = r#"
//!      (42, opt true, vec {1;2;3},
//!       opt record {label="text"; 42="haha"})
//!   "#;
//!
//!   // Parse text format into IDLArgs for serialization
//!   let args: IDLArgs = text_value.parse()?;
//!   let encoded: Vec<u8> = args.to_bytes()?;
//!
//!   // Deserialize into IDLArgs
//!   let decoded: IDLArgs = IDLArgs::from_bytes(&encoded)?;
//!   assert_eq!(args, decoded);
//!
//!   // Convert IDLArgs to text format
//!   let output: String = decoded.to_string();
//!   let parsed_args: IDLArgs = output.parse()?;
//!   assert_eq!(args, parsed_args);
//!   Ok(())
//! }
//! # untyped_examples().unwrap();
//! ```
//!
//! ## Operating on Candid AST
//!
//! ```
//! use candid::{IDLProg, Result, parser::types::to_pretty};
//! fn parser_examples() -> Result<()> {
//!   // .did file for actor signature. Most likely generated by dfx
//!   let did_file = r#"
//!     type List = record { head: int; tail: List };
//!     service : {
//!       f : (x: blob, opt bool) -> (variant { A; B; C });
//!       g : (List) -> (int) query;
//!     }
//!   "#;
//!
//!   // Parse did file into an AST
//!   let ast: IDLProg = did_file.parse()?;
//!
//!   // Pretty-print AST and access type definitions
//!   let pretty: String = to_pretty(&ast, 80);
//!   let showList = to_pretty(&ast.find_type("List")?, 80);
//!   let showMethod = to_pretty(&ast.get_method_type("g").unwrap(), 80);
//!   Ok(())
//! }
//! # parser_examples().unwrap();
//! ```
//!

pub use candid_derive::CandidType;
pub use serde::Deserialize;

pub mod error;
pub use error::{Error, Result};

pub mod number;
pub use number::{Int, Nat};

pub mod types;
pub use types::CandidType;

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

/// Encode sequence of Rust values into Candid message of type `candid::Result<Vec<u8>>`.
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

/// Decode Candid message into a tuple of Rust values of the given types.
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
