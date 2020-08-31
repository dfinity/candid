//! `candid::Result<T> = Result<T, candid::Error>>`

use serde::{de, ser};

use crate::parser::token;
use std::fmt::{self, Debug, Display};
use std::io;

pub type Result<T = ()> = std::result::Result<T, Error>;

#[derive(Clone)]
pub struct Error {
    pub message: String,
    states: String,
    pub span: token::Span,
}

impl Error {
    pub fn msg<T: Display>(msg: T) -> Self {
        Error {
            message: msg.to_string(),
            states: "".to_owned(),
            span: 0..0,
        }
    }
    pub fn msg_span<T: Display>(msg: T, span: token::Span) -> Self {
        Error {
            message: msg.to_string(),
            states: "".to_owned(),
            span,
        }
    }
    pub fn with_states(self, msg: String) -> Self {
        Error {
            message: self.message,
            states: msg,
            span: 0..0,
        }
    }
}

impl ser::Error for Error {
    fn custom<T: Display>(msg: T) -> Self {
        Error::msg(format!("Serialize error: {}", msg))
    }
}

impl de::Error for Error {
    fn custom<T: Display>(msg: T) -> Self {
        Error::msg(format!("Deserialize error: {}", msg))
    }
}

impl Display for Error {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.message)
    }
}

impl Debug for Error {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&format!("\nMessage: \"{}\"\n", self.message))?;
        if !self.states.is_empty() {
            formatter.write_str(&format!("States:\n{}\n", self.states))?;
        }
        Ok(())
    }
}

impl std::error::Error for Error {
    fn description(&self) -> &str {
        &self.message
    }
}

impl From<io::Error> for Error {
    fn from(e: io::Error) -> Error {
        Error::msg(format!("io error: {}", e))
    }
}

impl From<token::ParserError> for Error {
    fn from(e: token::ParserError) -> Error {
        use lalrpop_util::ParseError::*;
        let msg = format!("Candid parser error: {}", e);
        match e {
            User { error } => Error::msg_span(msg, error.span),
            InvalidToken { location } => Error::msg_span(msg, location..location + 1),
            UnrecognizedEOF {
                location,
                expected: _,
            } => Error::msg_span(msg, location..location + 1),
            UnrecognizedToken { token, expected: _ } => Error::msg_span(msg, token.0..token.2),
            ExtraToken { token } => Error::msg_span(msg, token.0..token.2),
        }
    }
}
