//! # Candid
//!
//! # Using the library
//!
//! ```
//! use candid::{Encode, Decode};
//! // Serialization
//! let bytes = Encode!(&[(42, "text")], &(42, "text"));
//! // Deserialization
//! Decode!(&bytes, a: Vec<(i64, &str)>, b: (i32, String));
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
//! Decode!(&bytes, l: List);
//!
//! let bytes2 = &Encode!(&list, &list);
//! Decode!(bytes2, l1:List, l2:List);
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
//! using the `DecodeResult` macro:
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
//!    Decoder!(&bytes, List, usize, List);
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

/// Decode IDL message into a sequence of Rust values.
/// Traps if the message fails to decode at the given types.
#[macro_export]
macro_rules! Decode {
    ( $hex:expr, $($name:ident: $ty:ty),* ) => {
        let mut de = candid::de::IDLDeserialize::new($hex);
        $(let $name: $ty = de.get_value().unwrap();)*
        de.done().unwrap()
    }
}

#[macro_export]
macro_rules! Decoder {
    ( $hex:expr $(,$ty:ty)* ) => {{
        let mut de = candid::de::IDLDeserialize::new($hex);
        let res = Decoder!(@GetValue [] de $($ty,)*);
        res
    }};
    (@GetValue [$($ans:ident)*] $de:ident) => {{
        Ok(($($ans),*))
    }};
    (@GetValue [$($ans:ident)*] $de:ident $ty:ty, $($tail:ty,)* ) => {{
        let x = $de.get_value::<$ty>();
        x.and_then(|val| Decoder!(@GetValue [val $($ans)*] $de $($tail,)* ))
    }};
}

/// Decode IDL message into an tuple of Rust values of the given types.
/// Produces `Err` if the message fails to decode at the given types.
#[macro_export]
macro_rules! DecodeResult {
    ( $hex:expr, $($name:ident: $ty:ty),* ) => {{
        let mut de = candid::de::IDLDeserialize::new($hex);
        $(let $name: Result<$ty,_> = de.get_value();)*
        let res_tup : Result<($($ty),*), candid::Error> =
            de.done().and_then(|_|
                               UnwrapTup!( $($name)* [])
            );
        res_tup
    }}
}

// Helper: Define inductive macro over a tuple of names;
//   unwrap each in the "result monad" and form a tuple of unwrapped results.
#[macro_export]
macro_rules! UnwrapTup {
    ( $name:ident $($rest:ident)* [ $($ans:ident)* ]) => {
        $name.and_then( |val|
                         UnwrapTup!( $($rest)* [ val $($ans)* ])
        )
    };
    ( [ $($ans:ident)* ]) => {
        Ok(($($ans),*))
    };
}
