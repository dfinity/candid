//! `candid::Result<T> = Result<T, candid::Error>>`

use serde::{de, ser};

use crate::parser::token;
use codespan_reporting::diagnostic::{Diagnostic, Label};
use std::fmt::{self, Debug, Display};
use std::io;

pub type Result<T = ()> = std::result::Result<T, Error>;

pub enum Error {
    Parse(token::ParserError),
    Deserialize(String, String),
    Custom(String),
}

impl Error {
    pub fn msg<T: Display>(msg: T) -> Self {
        Error::Custom(msg.to_string())
    }
    pub fn with_states(&self, states: String) -> Self {
        Error::Deserialize(self.to_string(), states)
    }
    pub fn report(&self) -> Diagnostic<()> {
        match self {
            Error::Parse(e) => {
                use lalrpop_util::ParseError::*;
                let mut diag = Diagnostic::error().with_message("parser error");
                let mut labels = Vec::new();
                let msg = format!("{}", e);
                match e {
                    User { error } => labels.push(
                        Label::primary((), error.span.clone()).with_message(error.err.clone()),
                    ),
                    InvalidToken { location } => {
                        labels.push(Label::primary((), *location..location + 1).with_message(msg))
                    }
                    UnrecognizedEOF {
                        location,
                        expected: _,
                    } => {
                        labels.push(Label::primary((), *location..location + 1).with_message(msg));
                    }
                    UnrecognizedToken { token, expected } => {
                        let msg = format!("Unrecognized token {:?}", token.1);
                        let mut expects = vec!["expect one of".to_owned()];
                        expects.extend_from_slice(expected);
                        labels.push(Label::primary((), token.0..token.2).with_message(msg));
                        diag = diag.with_notes(expects);
                    }
                    ExtraToken { token } => {
                        labels.push(Label::primary((), token.0..token.2).with_message(msg))
                    }
                }
                diag.with_labels(labels)
            }
            Error::Deserialize(e, _) => Diagnostic::error().with_message(e),
            Error::Custom(e) => Diagnostic::error().with_message(e),
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
        match self {
            Error::Parse(e) => formatter.write_str(&format!("Candid parser error: {}", e)),
            Error::Deserialize(e, _) => formatter.write_str(e),
            Error::Custom(e) => formatter.write_str(e),
        }
    }
}

impl Debug for Error {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(self, formatter)
    }
}

impl std::error::Error for Error {
    fn description(&self) -> &str {
        "candid error"
    }
}

impl From<io::Error> for Error {
    fn from(e: io::Error) -> Error {
        Error::msg(format!("io error: {}", e))
    }
}

impl From<token::ParserError> for Error {
    fn from(e: token::ParserError) -> Error {
        Error::Parse(e)
    }
}
