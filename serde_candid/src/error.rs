use serde::{de, ser};

use std::fmt::{self, Debug, Display};
use std::io;

pub type Result<T> = std::result::Result<T, Error>;

pub struct Error {
    message: String,
    states: String,
}

impl Error {
    pub fn msg<T: Display>(msg: T) -> Self {
        Error {
            message: msg.to_string(),
            states: "".to_owned(),
        }
    }
    pub fn with_states(self, msg: String) -> Self {
        Error {
            message: self.message,
            states: msg,
        }
    }
}

impl ser::Error for Error {
    fn custom<T: Display>(msg: T) -> Self {
        Error::msg(msg.to_string())
    }
}

impl de::Error for Error {
    fn custom<T: Display>(msg: T) -> Self {
        Error::msg(msg.to_string())
    }
}

impl Display for Error {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(std::error::Error::description(self))
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

impl From<crate::value::ParserError> for Error {
    fn from(e: crate::value::ParserError) -> Error {
        Error::msg(format!("IDL parser error: {}", e))
    }
}
