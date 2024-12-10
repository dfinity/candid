//! `candid::Result<T> = Result<T, candid::Error>>`

use serde::{de, ser};
use std::collections::TryReserveError;
use std::{io, num::ParseIntError};
use thiserror::Error;

pub type Result<T = ()> = std::result::Result<T, Error>;

#[derive(Debug)]
pub struct Label {
    pos: usize,
    message: String,
}

#[derive(Debug, Error)]
pub enum Error {
    #[error("binary parser error: {}", .0.first().map_or_else(|| "io error".to_string(), |f| format!("{} at byte offset {}", f.message, f.pos/2)))]
    Binread(Vec<Label>),

    #[error(transparent)]
    Reserve(#[from] TryReserveError),

    #[error("Subtyping error: {0}")]
    Subtype(String),

    #[error(transparent)]
    Custom(#[from] anyhow::Error),
}

impl Error {
    pub fn msg<T: ToString>(msg: T) -> Self {
        Error::Custom(anyhow::anyhow!(msg.to_string()))
    }
    pub fn subtype<T: ToString>(msg: T) -> Self {
        Error::Subtype(msg.to_string())
    }
}

fn get_binread_labels(e: &binread::Error) -> Vec<Label> {
    use binread::Error::*;
    match e {
        BadMagic { pos, .. } => {
            let pos = (pos * 2) as usize;
            vec![Label {
                pos,
                message: "Unexpected bytes".to_string(),
            }]
        }
        Custom { pos, err } => {
            let pos = (pos * 2) as usize;
            let err = err
                .downcast_ref::<&str>()
                .unwrap_or(&"unknown error (there's a bug in error reporting)");
            vec![Label {
                pos,
                message: (*err).to_string(),
            }]
        }
        EnumErrors {
            pos,
            variant_errors,
        } => {
            let pos = (pos * 2) as usize;
            let variant = variant_errors
                .iter()
                .find(|(_, e)| !matches!(e, BadMagic { .. }));
            // Should have at most one non-magic error
            match variant {
                None => vec![Label {
                    pos,
                    message: "Unknown opcode".to_string(),
                }],
                Some((id, e)) => {
                    let mut labels = get_binread_labels(e);
                    labels.push(Label {
                        pos,
                        message: (*id).to_string(),
                    });
                    labels
                }
            }
        }
        NoVariantMatch { pos } => {
            let pos = (pos * 2) as usize;
            vec![Label {
                pos,
                message: "No variant match".to_string(),
            }]
        }
        AssertFail { pos, message } => {
            let pos = (pos * 2) as usize;
            vec![Label {
                pos,
                message: message.to_string(),
            }]
        }
        Io(_) => vec![],
        _ => unreachable!(),
    }
}

impl ser::Error for Error {
    fn custom<T: std::fmt::Display>(msg: T) -> Self {
        Error::msg(format!("Serialize error: {msg}"))
    }
}

impl de::Error for Error {
    fn custom<T: std::fmt::Display>(msg: T) -> Self {
        let msg = msg.to_string();
        if let Some(msg) = msg.strip_prefix("Subtyping error: ") {
            Error::Subtype(msg.to_string())
        } else {
            Error::msg(format!("Deserialize error: {msg}"))
        }
    }
    fn invalid_type(_: de::Unexpected<'_>, exp: &dyn de::Expected) -> Self {
        Error::Subtype(format!("{exp}"))
    }
}

impl From<io::Error> for Error {
    fn from(e: io::Error) -> Error {
        Error::msg(format!("io error: {e}"))
    }
}

impl From<binread::Error> for Error {
    fn from(e: binread::Error) -> Error {
        Error::Binread(get_binread_labels(&e))
    }
}

impl From<ParseIntError> for Error {
    fn from(e: ParseIntError) -> Error {
        Error::msg(format!("ParseIntError: {e}"))
    }
}
