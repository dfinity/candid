//! # Candid
//!
//! # Using the library
//!
//! ```
//! use candid::{Encode, Decode};
//! // Serialization
//! let bytes = Encode!(&[(42, "text")], &(42, "text"));
//! // Deserialization
//! let (a, b) = Decode!(&bytes, Vec<(i64, &str)>, (i32, String)).unwrap();
//! assert_eq!(a, [(42, "text")]);
//! assert_eq!(b, (42i32, "text".to_string()));
//! ```
//!
//! # Serialize/Deserialize struct/enum
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
//! let bytes = Encode!(&list);
//! let res = Decode!(&bytes, List).unwrap();
//!
//! ```
//!
//! # Operating on untyped IDL values
//!
//! ## Option 1: Represent decoded message with `IDLArgs` type
//!
//! Any valid IDL message can be manipulated in the `IDLArgs` data structure, which contains
//! a vector of untyped enum structure called `IDLValue`.
//!
//! `IDLArgs` supports both binary and textual IDL format.
//! As an example, the following assertions should always be true.
//!
//! ```
//! use candid::{IDLArgs};
//! let idl_text = "(42,opt true, vec {1;2;3}, opt record {label=\"text\"; 42=\"haha\"})";
//! let args: IDLArgs = idl_text.parse().unwrap();
//! let encoded: Vec<u8> = args.to_bytes().unwrap();
//! let decoded: IDLArgs = IDLArgs::from_bytes(&encoded).unwrap();
//! assert_eq!(args, decoded);
//! let output: String = decoded.to_string();
//! let back_args: IDLArgs = output.parse().unwrap();
//! assert_eq!(args, back_args);
//! ```
//!
//! ## Option 2: Represent decoded message with a `Result` type in Rust
//!
//! In some generic tooling scenarios, the message may have an _unknown_ Rust type (or none at all),
//! but it may also have a Rust type that is known, and either case is possible.
//!
//! Imagine a tool that intercepts and displays special log messages, but ignores all others.
//!
//! In these scenarios, the program may wish to distinguish the known and uknown cases
//! by decoding into an a Rust `Result` type,
//! using the `Decode` macro:
//!
//! ```
//! # #[macro_use] extern crate candid;
//! #[derive(CandidType, Deserialize, Debug)]
//! struct List {
//!     head: i32,
//!     tail: Option<Box<List>>,
//! }
//! let list = List { head: 42, tail: None };
//! let num : usize = 42;
//! let bytes = &Encode!(&list, &num, &list);
//! let lists_res : Result<(List, usize, List), _> =
//!    Decode!(&bytes, List, usize, List);
//! ```

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

// IDL hash function comes from
// https://caml.inria.fr/pub/papers/garrigue-polymorphic_variants-ml98.pdf
pub fn idl_hash(id: &str) -> u32 {
    let mut s: u32 = 0;
    for c in id.chars() {
        s = s.wrapping_mul(223).wrapping_add(c as u32);
    }
    s
}

/// Encode sequence of Rust values into IDL message.
#[macro_export]
macro_rules! Encode {
    ( $($x:expr),* ) => {{
        let mut idl = candid::ser::IDLBuilder::new();
        $(idl.arg($x).unwrap();)*
        idl.serialize_to_vec().unwrap()
    }}
}

/// Decode IDL message into an tuple of Rust values of the given types.
/// Produces `Err` if the message fails to decode at any given types.
/// If the message contains only one value, it returns the value directly instead of a tuple.
#[macro_export]
macro_rules! Decode {
    ( $hex:expr $(,$ty:ty)* ) => {{
        candid::de::IDLDeserialize::new($hex)
            .and_then(|mut de| Decode!(@GetValue [] de $($ty,)*)
                      .and_then(|res| de.done().and(Ok(res))))
    }};
    (@GetValue [$($ans:ident)*] $de:ident) => {{
        Ok(($($ans),*))
    }};
    (@GetValue [$($ans:ident)*] $de:ident $ty:ty, $($tail:ty,)* ) => {{
        $de.get_value::<$ty>()
            .and_then(|val| Decode!(@GetValue [$($ans)* val] $de $($tail,)* ))
    }};
}
