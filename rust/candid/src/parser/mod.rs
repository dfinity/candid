//! Provides parser for Candid type and value.
//!  * `str.parse::<IDLProg>()` parses the Candid signature file to Candid AST.
//!  * `str.parse::<IDLArgs>()` parses the Candid value in text format to a struct `IDLArg` that can be used for serialization and deserialization between Candid and an enum type `IDLValue` in Rust.

pub mod grammar;

pub mod token;
pub mod types;

pub mod typing;

#[cfg(feature = "configs")]
pub mod configs;
#[cfg(feature = "random")]
pub mod random;
pub mod test;

pub use crate::types::value::{IDLArgs, IDLValue};

impl std::str::FromStr for IDLArgs {
    type Err = crate::Error;
    fn from_str(str: &str) -> std::result::Result<Self, Self::Err> {
        let lexer = token::Tokenizer::new(str);
        Ok(grammar::ArgsParser::new().parse(lexer)?)
    }
}

impl std::str::FromStr for IDLValue {
    type Err = crate::Error;
    fn from_str(str: &str) -> std::result::Result<Self, Self::Err> {
        let lexer = token::Tokenizer::new(str);
        Ok(grammar::ArgParser::new().parse(lexer)?)
    }
}
