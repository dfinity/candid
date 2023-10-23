//! `candid::Result<T> = Result<T, candid::Error>>`

use codespan_reporting::diagnostic::Label;
use serde::{de, ser};
use std::{io, num::ParseIntError};
use thiserror::Error;

pub type Result<T = ()> = std::result::Result<T, Error>;

#[derive(Debug, Error)]
pub enum Error {
    #[error("binary parser error: {}", .0.get(0).map(|f| format!("{} at byte offset {}", f.message, f.range.start/2)).unwrap_or_else(|| "io error".to_string()))]
    Binread(Vec<Label<()>>),

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

fn get_binread_labels(e: &binread::Error) -> Vec<Label<()>> {
    use binread::Error::*;
    match e {
        BadMagic { pos, .. } => {
            let pos = (pos * 2) as usize;
            vec![Label::primary((), pos..pos + 2).with_message("Unexpected bytes")]
        }
        Custom { pos, err } => {
            let pos = (pos * 2) as usize;
            let err = err
                .downcast_ref::<&str>()
                .unwrap_or(&"unknown error (there's a bug in error reporting)");
            vec![Label::primary((), pos..pos + 2).with_message(err.to_string())]
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
                None => vec![Label::primary((), pos..pos + 2).with_message("Unknown opcode")],
                Some((id, e)) => {
                    let mut labels = get_binread_labels(e);
                    labels.push(Label::secondary((), pos..pos + 2).with_message(id.to_string()));
                    labels
                }
            }
        }
        NoVariantMatch { pos } => {
            let pos = (pos * 2) as usize;
            vec![Label::primary((), pos..pos + 2).with_message("No variant match")]
        }
        AssertFail { pos, message } => {
            let pos = (pos * 2) as usize;
            vec![Label::primary((), pos..pos + 2).with_message(message)]
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
