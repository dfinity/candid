//! Provides parser for Candid type and value.
//!  * `str.parse::<IDLProg>()` parses the Candid signature file to Candid AST.
//!  * `parse_idl_args()` parses the Candid value in text format to a struct `IDLArg` that can be used for serialization and deserialization between Candid and an enum type `IDLValue` in Rust.

pub mod grammar;

pub mod token;
pub mod types;

pub mod typing;

#[cfg_attr(docsrs, doc(cfg(feature = "configs")))]
#[cfg(feature = "configs")]
pub mod configs;
#[cfg_attr(docsrs, doc(cfg(feature = "random")))]
#[cfg(feature = "random")]
pub mod random;
pub mod test;

pub fn parse_idl_args(s: &str) -> crate::Result<candid::IDLArgs> {
    let lexer = token::Tokenizer::new(s);
    Ok(grammar::ArgsParser::new().parse(lexer)?)
}

pub fn parse_idl_value(s: &str) -> crate::Result<candid::IDLValue> {
    let lexer = token::Tokenizer::new(s);
    Ok(grammar::ArgParser::new().parse(lexer)?)
}