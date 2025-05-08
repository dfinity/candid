//! # Candid
//!
//! Candid is an interface description language (IDL) for interacting with _canisters_ (also known as _services_ or _actors_) running on the Internet Computer.
//!
//! There are three common ways that you might find yourself needing to work with Candid in Rust.
//! - As a typed Rust data structure. When you write canisters or frontend in Rust, you want to have a seamless way of converting data between Rust and Candid.
//! - As an untyped Candid value. When you write generic tools for the Internet Computer without knowing the type of the Candid data.
//! - As text data. When you get the data from CLI or read from a file, you can use the provided parser to send/receive messages.
//!
//! Candid provides efficient, flexible and safe ways of converting data between each of these representations.
//!
//! ## Operating on native Rust values
//! We are using a builder pattern to encode/decode Candid messages, see [`candid::ser::IDLBuilder`](ser/struct.IDLBuilder.html) for serialization and [`candid::de::IDLDeserialize`](de/struct.IDLDeserialize.html) for deserialization.
//!
//! ```
//! // Serialize 10 numbers to Candid binary format
//! let mut ser = candid::ser::IDLBuilder::new();
//! for i in 0..10 {
//!   ser.arg(&i)?;
//! }
//! let bytes: Vec<u8> = ser.serialize_to_vec()?;
//!
//! // Deserialize Candid message and verify the values match
//! let mut de = candid::de::IDLDeserialize::new(&bytes)?;
//! let mut i = 0;
//! while !de.is_done() {
//!   let x = de.get_value::<i32>()?;
//!   assert_eq!(x, i);
//!   i += 1;
//! }
//! de.done()?;
//! # Ok::<(), candid::Error>(())
//! ```
//!
//! Candid provides functions for encoding/decoding a Candid message in a type-safe way.
//!
//! ```
//! use candid::{encode_args, decode_args};
//! // Serialize two values [(42, "text")] and (42u32, "text")
//! let bytes: Vec<u8> = encode_args((&[(42, "text")], &(42u32, "text")))?;
//! // Deserialize the first value as type Vec<(i32, &str)>,
//! // and the second value as type (u32, String)
//! let (a, b): (Vec<(i32, &str)>, (u32, String)) = decode_args(&bytes)?;
//!
//! assert_eq!(a, [(42, "text")]);
//! assert_eq!(b, (42u32, "text".to_string()));
//! # Ok::<(), candid::Error>(())
//! ```
//!
//! We also provide macros for encoding/decoding Candid message in a convenient way.
//!
//! ```
//! use candid::{Encode, Decode};
//! // Serialize two values [(42, "text")] and (42u32, "text")
//! let bytes: Vec<u8> = Encode!(&[(42, "text")], &(42u32, "text"))?;
//! // Deserialize the first value as type Vec<(i32, &str)>,
//! // and the second value as type (u32, String)
//! let (a, b) = Decode!(&bytes, Vec<(i32, &str)>, (u32, String))?;
//!
//! assert_eq!(a, [(42, "text")]);
//! assert_eq!(b, (42u32, "text".to_string()));
//! # Ok::<(), candid::Error>(())
//! ```
//!
//! The [`Encode!`](macro.Encode.html) macro takes a sequence of Rust values, and returns a binary format `Vec<u8>` that can be sent over the wire.
//! The [`Decode!`](macro.Decode.html) macro takes the binary message and a sequence of Rust types that you want to decode into, and returns a tuple
//! of Rust values of the given types.
//!
//! Note that a fixed Candid message may be decoded in multiple Rust types. For example,
//! we can decode a Candid `text` type into either `String` or `&str` in Rust.
//!
//! ## Operating on user defined struct/enum
//! We use trait [`CandidType`](types/trait.CandidType.html) for serialization. Deserialization requires both [`CandidType`](types/trait.CandidType.html) and Serde's [`Deserialize`](trait.Deserialize.html) trait.
//! Any type that implements these two traits can be used for serialization and deserialization.
//! This includes built-in Rust standard library types like `Vec<T>` and `Result<T, E>`, as well as any structs
//! or enums annotated with `#[derive(CandidType, Deserialize)]`.
//!
//! We do not use Serde's `Serialize` trait because Candid requires serializing types along with the values.
//! This is difficult to achieve in `Serialize`, especially for enum types. Besides serialization, [`CandidType`](types/trait.CandidType.html)
//! trait also converts Rust type to Candid type defined as [`candid::types::Type`](types/internal/enum.Type.html).
//! ```
//! #[cfg(feature = "serde_bytes")]
//! # fn f() -> Result<(), candid::Error> {
//! use candid::{Encode, Decode, CandidType, Deserialize};
//! #[derive(CandidType, Deserialize)]
//! # #[derive(Debug, PartialEq)]
//! enum List {
//!     #[serde(rename = "nil")]
//!     Nil,
//!     #[serde(with = "serde_bytes")]
//!     Node(Vec<u8>),
//!     Cons(i32, Box<List>),
//! }
//! let list = List::Cons(42, Box::new(List::Nil));
//!
//! let bytes = Encode!(&list)?;
//! let res = Decode!(&bytes, List)?;
//! assert_eq!(res, list);
//! # Ok(())
//! # }
//! ```
//! We support serde's rename attributes for each field, namely `#[serde(rename = "foo")]`
//! and `#[serde(rename(serialize = "foo", deserialize = "foo"))]`.
//! This is useful when interoperating between Rust and Motoko canisters involving variant types, because
//! they use different naming conventions for field names.
//!
//! We support `#[serde(with = "serde_bytes")]` for efficient handling of `&[u8]` and `Vec<u8>`. You can
//! also use the wrapper type `serde_bytes::ByteBuf` and `serde_bytes::Bytes`.
//!
//! Note that if you are deriving `Deserialize` trait from Candid, you need to import `serde` as a dependency in
//! your project, as the derived implementation will refer to the `serde` crate.
//!
//! ## Operating on big integers
//! To support big integer types [`Candid::Int`](types/number/struct.Int.html) and [`Candid::Nat`](types/number/struct.Nat.html),
//! we use the `num_bigint` crate. We provide interface to convert `i64`, `u64`, `&str` and `&[u8]` to big integers.
//! You can also use `i128` and `u128` to represent Candid `int` and `nat` types respectively (decoding will fail if
//! the number is more than 128 bits).
//! ```
//! #[cfg(feature = "bignum")]
//! # fn f() -> Result<(), candid::Error> {
//! use candid::{Int, Nat, Encode, Decode};
//! let x = "-10000000000000000000".parse::<Int>()?;
//! let bytes = Encode!(&Nat::from(1024u32), &x)?;
//! let (a, b) = Decode!(&bytes, Nat, Int)?;
//! let (c, d) = Decode!(&bytes, u128, i128)?;
//! assert_eq!(a + 1u8, 1025u32);
//! assert_eq!(b, Int::parse(b"-10000000000000000000")?);
//! # Ok(())
//! # }
//! ```
//!
//! ## Operating on reference types
//! The type of function and service references cannot be derived automatically. We provide
//! two macros [`define_function!`](macro.define_function.html) and [`define_service!`](macro.define_service.html) to help defining the reference types. To specify reference types in the macro, you need to use the corresponding Rust types,
//! instead of the Candid types.
//!
//! ```
//! #[cfg(feature = "bignum")]
//! # fn f() -> Result<(), candid::Error> {
//! use candid::{define_function, define_service, func, Encode, Decode, Principal};
//! let principal = Principal::from_text("aaaaa-aa").unwrap();
//!
//! define_function!(pub CustomFunc : (u8, &str) -> (u128));
//! let func = CustomFunc::new(principal, "method_name".to_string());
//! assert_eq!(func, Decode!(&Encode!(&func)?, CustomFunc)?);
//!
//! define_service!(MyService : {
//!   "f": CustomFunc::ty();
//!   "g": func!((candid::Int) -> (candid::Nat, CustomFunc) query)
//! });
//! let serv = MyService::new(principal);
//! assert_eq!(serv, Decode!(&Encode!(&serv)?, MyService)?);
//! # Ok(())
//! # }
//! ```
//!
//! ## Operating on untyped Candid values
//! Any valid Candid value can be manipulated in an recursive enum representation [`candid::parser::value::IDLValue`](parser/value/enum.IDLValue.html).
//! We use `ser.value_arg(v)` and `de.get_value::<IDLValue>()` for encoding and decoding the value.
//! The use of Rust value and `IDLValue` can be intermixed.
//!
//! ```
//! #[cfg(feature = "value")]
//! # fn f() -> Result<(), candid::Error> {
//! use candid::types::value::IDLValue;
//! // Serialize Rust value Some(42u8) and IDLValue "hello"
//! let bytes = candid::ser::IDLBuilder::new()
//!     .arg(&Some(42u8))?
//!     .value_arg(&IDLValue::Text("hello".to_string()))?
//!     .serialize_to_vec()?;
//!
//! // Deserialize the first Rust value into IDLValue,
//! // and the second IDLValue into Rust value
//! let mut de = candid::de::IDLDeserialize::new(&bytes)?;
//! let x = de.get_value::<IDLValue>()?;
//! let y = de.get_value::<&str>()?;
//! de.done()?;
//!
//! assert_eq!(x, IDLValue::Opt(Box::new(IDLValue::Nat8(42))));
//! assert_eq!(y, "hello");
//! # Ok(())
//! # }
//! ```
//!
//! ## Building the library as a JS/Wasm package
//! With the help of `wasm-bindgen` and `wasm-pack`, we can build the library as a Wasm binary and run in the browser.
//! This is useful for client-side UIs and parsing did files in JavaScript.
//!
//! Create a new project with the following `Cargo.toml`.
//! ```toml
//! [lib]
//! crate-type = ["cdylib"]
//!
//! [dependencies]
//! wasm-bindgen = "0.2"
//! candid = "0.9.0"
//! candid_parser = "0.1.0"
//!
//! [profile.release]
//! lto = true
//! opt-level = 'z'
//! ```
//! Expose the methods in `lib.rs`
//! ```ignore
//! use candid::TypeEnv;
//! use candid_parser::{check_prog, IDLProg};
//! use wasm_bindgen::prelude::*;
//! #[wasm_bindgen]
//! pub fn did_to_js(prog: String) -> Option<String> {
//!   let ast = prog.parse::<IDLProg>().ok()?;
//!   let mut env = TypeEnv::new();
//!   let actor = check_prog(&mut env, &ast).ok()?;
//!   Some(candid_parser::bindings::javascript::compile(&env, &actor))
//! }
//! ```
//! ### Building
//! ```shell
//! cargo install wasm-pack
//! wasm-pack build --target bundler
//! wasm-opt --strip-debug -Oz pkg/didc_bg.wasm -o pkg/didc_bg.wasm
//! ```
//! ### Usage
//! ```js
//! const didc = import("pkg/didc");
//! didc.then((mod) => {
//!   const service = "service : {}";
//!   const js = mod.did_to_js(service);
//! });
//! ```
//!
//!

// only enables the `doc_cfg` feature when
// the `docsrs` configuration attribute is defined
#![cfg_attr(docsrs, feature(doc_cfg))]

pub use candid_derive::{candid_method, export_service, CandidType};
pub use serde::Deserialize;

pub mod error;
pub use error::{Error, Result};

pub mod types;
#[cfg(feature = "bignum")]
pub use types::number::{Int, Nat};
pub use types::CandidType;
pub use types::{
    arc,
    principal::Principal,
    rc,
    reference::{Func, Service},
    reserved::{Empty, Reserved},
    result::MotokoResult,
    TypeEnv,
};

#[allow(dead_code)]
pub mod binary_parser;
pub mod de;
pub use de::DecoderConfig;
pub mod ser;

pub mod utils;
pub use utils::{
    decode_args, decode_args_with_config, decode_args_with_decoding_and_skipping_quota,
    decode_args_with_decoding_quota, decode_args_with_skipping_quota, decode_one,
    decode_one_with_config, decode_one_with_decoding_and_skipping_quota,
    decode_one_with_decoding_quota, decode_one_with_skipping_quota, encode_args, encode_one,
    write_args,
};

#[cfg_attr(docsrs, doc(cfg(feature = "value")))]
#[cfg(feature = "value")]
pub use types::value::{IDLArgs, IDLValue};
#[cfg_attr(docsrs, doc(cfg(feature = "printer")))]
#[cfg(feature = "printer")]
pub mod pretty;

// Candid hash function comes from
// https://caml.inria.fr/pub/papers/garrigue-polymorphic_variants-ml98.pdf
// Not public API. Only used by tests.
// Remember to update the same function in candid_derive if you change this function.
#[doc(hidden)]
#[inline]
pub fn idl_hash(id: &str) -> u32 {
    let mut s: u32 = 0;
    for c in id.as_bytes() {
        s = s.wrapping_mul(223).wrapping_add(*c as u32);
    }
    s
}
