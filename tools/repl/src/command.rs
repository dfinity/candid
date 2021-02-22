use super::token::{ParserError, Spanned, Tokenizer};
use candid::parser::value::IDLValue;
use candid::Principal;

#[derive(Debug)]
pub enum Command {
    Call {
        canister: Spanned<Principal>,
        method: String,
        args: Vec<IDLValue>,
    },
    Config(String),
}

impl std::str::FromStr for Command {
    type Err = ParserError;
    fn from_str(str: &str) -> Result<Self, Self::Err> {
        let lexer = Tokenizer::new(str);
        super::grammar::CommandParser::new().parse(lexer)
    }
}
