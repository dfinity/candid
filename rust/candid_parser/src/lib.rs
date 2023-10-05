//! # Candid Parser
//!
//! ## Parse [`candid::IDLArgs`]
//!
//! We provide a parser to parse Candid values in text format.
//!
//! ```
//! # fn f() -> anyhow::Result<()> {
//! use candid::{IDLArgs, TypeEnv};
//! use candid_parser::parser::parse_idl_args;
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
//! use candid_parser::{IDLProg, check_prog};
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
//! let ast: IDLProg = did_file.parse()?;
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
//! assert_eq!(method.args, vec![TypeInner::Var("List".to_string()).into()]);
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
//! use candid_parser::parser::parse_idl_args;
//! # use candid::TypeEnv;
//! # use candid_parser::{IDLProg, check_prog};
//! # let did_file = r#"
//! #    type List = opt record { head: int; tail: List };
//! #    type byte = nat8;
//! #    service : {
//! #      f : (byte, int, nat, int8) -> (List);
//! #      g : (List) -> (int) query;
//! #    }
//! # "#;
//! # let ast = did_file.parse::<IDLProg>()?;
//! # let mut env = TypeEnv::new();
//! # let actor = check_prog(&mut env, &ast)?.unwrap();
//! // Get method type f : (byte, int, nat, int8) -> (List)
//! let method = env.get_method(&actor, "f").unwrap();
//! let args = parse_idl_args("(42, 42, 42, 42)")?;
//! // Serialize arguments with candid types
//! let encoded = args.to_bytes_with_types(&env, &method.args)?;
//! let decoded = IDLArgs::from_bytes(&encoded)?;
//! assert_eq!(decoded.args,
//!        vec![IDLValue::Nat8(42),
//!             IDLValue::Int(42.into()),
//!             IDLValue::Nat(42.into()),
//!             IDLValue::Int8(42)
//!            ]);
//! # Ok(())
//! # }
//! ```

// only enables the `doc_cfg` feature when
// the `docsrs` configuration attribute is defined
#![cfg_attr(docsrs, feature(doc_cfg))]

pub mod error;
pub use error::{Error, Result};

pub mod parser;
pub use error::pretty_parse;
pub use parser::{
    types::IDLProg,
    typing::{check_file, check_prog, pretty_check_file},
};

pub mod bindings;

pub mod utils;
