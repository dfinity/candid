//! # Candid Parser
//!
//! Everything from `candid` crate is re-exported here. Users don't have to add `candid` as their dependency in `Cargo.toml`.
//!
//! Provides parser for Candid type and value.
//!  * `str.parse::<IDLProg>()` parses the Candid signature file to Candid AST.
//!  * `parse_idl_args()` parses the Candid value in text format to a struct `IDLArg` that can be used for serialization and deserialization between Candid and an enum type `IDLValue` in Rust.

//! ## Parse [`candid::IDLArgs`]
//!
//! We provide a parser to parse Candid values in text format.
//!
//! ```
//! # fn f() -> anyhow::Result<()> {
//! use candid::{IDLArgs, TypeEnv};
//! use candid_parser::parse_idl_args;
//! // Candid values represented in text format
//! let text_value = r#"
//!      (42, opt true, vec {1;2;3},
//!       opt record {label="text"; 42="haha"})
//! "#;
//!
//! // Parse text format into IDLArgs for serialization
//! let args: IDLArgs = parse_idl_args(text_value)?;
//! let encoded: Vec<u8> = args.to_bytes()?;
//!
//! // Deserialize into IDLArgs
//! let decoded: IDLArgs = IDLArgs::from_bytes(&encoded)?;
//! assert_eq!(encoded, decoded.to_bytes()?);
//!
//! // Convert IDLArgs to text format
//! let output: String = decoded.to_string();
//! let parsed_args: IDLArgs = parse_idl_args(&output)?;
//! let annotated_args = args.annotate_types(true, &TypeEnv::new(), &parsed_args.get_types())?;
//! assert_eq!(annotated_args, parsed_args);
//! # Ok(())
//! # }
//! ```
//! Note that when parsing Candid values, we assume the number literals are always of type `Int`.
//! This can be changed by providing the type of the method arguments, which can usually be obtained
//! by parsing a Candid file in the following section.
//!
//! ## Operating on Candid AST
//!
//! We provide a parser and type checker for Candid files specifying the service interface.
//!
//! ```
//! # fn f() -> anyhow::Result<()> {
//! use candid::{TypeEnv, types::{Type, TypeInner}};
//! use candid_parser::{check_prog, parse_idl_prog};
//! let did_file = r#"
//!     type List = opt record { head: int; tail: List };
//!     type byte = nat8;
//!     service : {
//!       f : (byte, int, nat, int8) -> (List);
//!       g : (List) -> (int) query;
//!     }
//! "#;
//!
//! // Parse did file into an AST
//! let ast = parse_idl_prog(did_file)?;
//!
//! // Type checking a given .did file
//! // let (env, opt_actor) = check_file("a.did")?;
//! // Or alternatively, use check_prog to check in-memory did file
//! // Note that file import is ignored by check_prog.
//! let mut env = TypeEnv::new();
//! let actor: Type = check_prog(&mut env, &ast)?.unwrap();
//!
//! let method = env.get_method(&actor, "g").unwrap();
//! assert_eq!(method.is_query(), true);
//! assert_eq!(method.args.iter().map(|arg| arg.typ.clone()).collect::<Vec<_>>(), vec![TypeInner::Var("List".to_string()).into()]);
//! # Ok(())
//! # }
//! ```
//!
//! ## Serializing untyped Candid values with type annotations.
//!
//! With type signatures from the Candid file, [`candid::IDLArgs`](parser/value/struct.IDLArgs.html)
//! uses `to_bytes_with_types` function to serialize arguments directed by the Candid types.
//! This is useful when serializing different number types and recursive types.
//! There is no need to use types for deserialization as the types are available in the Candid message.
//!
//! ```
//! # fn f() -> anyhow::Result<()> {
//! use candid::{IDLArgs, types::value::IDLValue};
//! use candid_parser::parse_idl_args;
//! # use candid::TypeEnv;
//! # use candid_parser::{check_prog, parse_idl_prog};
//! # let did_file = r#"
//! #    type List = opt record { head: int; tail: List };
//! #    type byte = nat8;
//! #    service : {
//! #      f : (byte, int, nat, int8) -> (List);
//! #      g : (List) -> (int) query;
//! #    }
//! # "#;
//! # let ast = parse_idl_prog(did_file)?;
//! # let mut env = TypeEnv::new();
//! # let actor = check_prog(&mut env, &ast)?.unwrap();
//! // Get method type f : (byte, int, nat, int8) -> (List)
//! let method = env.get_method(&actor, "f").unwrap();
//! let args = parse_idl_args("(42, 42, 42, 42)")?;
//! // Serialize arguments with candid types
//! let encoded = args.to_bytes_with_types(&env, &method.args.iter().map(|arg| arg.typ.clone()).collect::<Vec<_>>())?;
//! let decoded = IDLArgs::from_bytes(&encoded)?;
//! assert_eq!(decoded.args,
//!        vec![IDLValue::Nat8(42),
//!             IDLValue::Int(42.into()),
//!             IDLValue::Nat(42u8.into()),
//!             IDLValue::Int8(42)
//!            ]);
//! # Ok(())
//! # }
//! ```

// only enables the `doc_cfg` feature when
// the `docsrs` configuration attribute is defined
#![cfg_attr(docsrs, feature(doc_cfg))]

pub mod error;
pub use error::{
    pretty_parse, pretty_parse_idl_prog, pretty_parse_idl_types, pretty_wrap, Error, Result,
};

pub mod bindings;
pub mod grammar;
pub mod token;
pub mod typing;
pub mod utils;
pub use typing::{check_file, check_prog, pretty_check_file};

pub use candid;
pub use candid::*;

#[cfg_attr(docsrs, doc(cfg(feature = "assist")))]
#[cfg(feature = "assist")]
pub mod assist;
pub mod configs;
#[cfg_attr(docsrs, doc(cfg(feature = "random")))]
#[cfg(feature = "random")]
pub mod random;
pub mod test;

pub fn parse_idl_prog(str: &str) -> Result<candid::types::syntax::IDLProg> {
    let trivia = token::TriviaMap::default();
    let lexer = token::Tokenizer::new_with_trivia(str, trivia.clone());
    let res = grammar::IDLProgParser::new().parse(Some(&trivia.clone()), lexer)?;
    Ok(res)
}

pub fn parse_idl_init_args(str: &str) -> Result<candid::types::syntax::IDLInitArgs> {
    let lexer = token::Tokenizer::new(str);
    Ok(grammar::IDLInitArgsParser::new().parse(None, lexer)?)
}

pub fn parse_idl_type(str: &str) -> Result<candid::types::syntax::IDLType> {
    let lexer = token::Tokenizer::new(str);
    Ok(grammar::TypParser::new().parse(None, lexer)?)
}

pub fn parse_idl_types(str: &str) -> Result<candid::types::syntax::IDLTypes> {
    let lexer = token::Tokenizer::new(str);
    Ok(grammar::TypsParser::new().parse(None, lexer)?)
}

pub fn parse_idl_args(s: &str) -> crate::Result<candid::IDLArgs> {
    let lexer = token::Tokenizer::new(s);
    Ok(grammar::ArgsParser::new().parse(None, lexer)?)
}

pub fn parse_idl_value(s: &str) -> crate::Result<candid::IDLValue> {
    let lexer = token::Tokenizer::new(s);
    Ok(grammar::ArgParser::new().parse(None, lexer)?)
}
