pub mod grammar;
pub mod lexer;
pub mod types;
pub mod value;

pub type ParserError = lalrpop_util::ParseError<usize, lexer::Token, lexer::LexicalError>;
