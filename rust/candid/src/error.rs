//! `candid::Result<T> = Result<T, candid::Error>>`

use codespan_reporting::diagnostic::Label;
use serde::{de, ser};
use std::io;
use thiserror::Error;

#[cfg(feature = "parser")]
use crate::parser::token;
#[cfg(feature = "parser")]
use codespan_reporting::{
    diagnostic::Diagnostic,
    files::{Error as ReportError, SimpleFile},
    term::{self, termcolor::StandardStream},
};

pub type Result<T = ()> = std::result::Result<T, Error>;

#[derive(Debug, Error)]
pub enum Error {
    #[cfg_attr(docsrs, doc(cfg(feature = "parser")))]
    #[cfg(feature = "parser")]
    #[error("Candid parser error: {0}")]
    Parse(#[from] token::ParserError),

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
    #[cfg_attr(docsrs, doc(cfg(feature = "parser")))]
    #[cfg(feature = "parser")]
    pub fn report(&self) -> Diagnostic<()> {
        match self {
            Error::Parse(e) => {
                use lalrpop_util::ParseError::*;
                let mut diag = Diagnostic::error().with_message("parser error");
                let label = match e {
                    User { error } => {
                        Label::primary((), error.span.clone()).with_message(&error.err)
                    }
                    InvalidToken { location } => {
                        Label::primary((), *location..location + 1).with_message("Invalid token")
                    }
                    UnrecognizedEOF { location, expected } => {
                        diag = diag.with_notes(report_expected(expected));
                        Label::primary((), *location..location + 1).with_message("Unexpected EOF")
                    }
                    UnrecognizedToken { token, expected } => {
                        diag = diag.with_notes(report_expected(expected));
                        Label::primary((), token.0..token.2).with_message("Unexpected token")
                    }
                    ExtraToken { token } => {
                        Label::primary((), token.0..token.2).with_message("Extra token")
                    }
                };
                diag.with_labels(vec![label])
            }
            Error::Binread(labels) => {
                let diag = Diagnostic::error().with_message("decoding error");
                diag.with_labels(labels.to_vec())
            }
            Error::Subtype(e) => Diagnostic::error().with_message(e),
            Error::Custom(e) => Diagnostic::error().with_message(e.to_string()),
        }
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

#[cfg_attr(docsrs, doc(cfg(feature = "parser")))]
#[cfg(feature = "parser")]
fn report_expected(expected: &[String]) -> Vec<String> {
    if expected.is_empty() {
        return Vec::new();
    }
    use pretty::RcDoc;
    let doc: RcDoc<()> = RcDoc::intersperse(
        expected.iter().map(RcDoc::text),
        RcDoc::text(",").append(RcDoc::softline()),
    );
    let header = if expected.len() == 1 {
        "Expects"
    } else {
        "Expects one of"
    };
    let doc = RcDoc::text(header).append(RcDoc::softline().append(doc));
    vec![doc.pretty(70).to_string()]
}

impl ser::Error for Error {
    fn custom<T: std::fmt::Display>(msg: T) -> Self {
        Error::msg(format!("Serialize error: {msg}"))
    }
}

impl de::Error for Error {
    fn custom<T: std::fmt::Display>(msg: T) -> Self {
        Error::msg(format!("Deserialize error: {msg}"))
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
#[cfg_attr(docsrs, doc(cfg(feature = "parser")))]
#[cfg(feature = "parser")]
impl From<ReportError> for Error {
    fn from(e: ReportError) -> Error {
        Error::msg(e)
    }
}
#[cfg_attr(docsrs, doc(cfg(feature = "random")))]
#[cfg(feature = "random")]
impl From<arbitrary::Error> for Error {
    fn from(e: arbitrary::Error) -> Error {
        Error::msg(format!("arbitrary error: {e}"))
    }
}

#[cfg_attr(docsrs, doc(cfg(feature = "configs")))]
#[cfg(feature = "configs")]
impl From<serde_dhall::Error> for Error {
    fn from(e: serde_dhall::Error) -> Error {
        Error::msg(format!("dhall error: {e}"))
    }
}

#[cfg_attr(docsrs, doc(cfg(feature = "parser")))]
#[cfg(feature = "parser")]
pub fn pretty_parse<T>(name: &str, str: &str) -> Result<T>
where
    T: std::str::FromStr<Err = Error>,
{
    str.parse::<T>().or_else(|e| {
        let writer = StandardStream::stderr(term::termcolor::ColorChoice::Auto);
        let config = term::Config::default();
        let file = SimpleFile::new(name, str);
        term::emit(&mut writer.lock(), &config, &file, &e.report())?;
        Err(e)
    })
}
#[cfg_attr(docsrs, doc(cfg(feature = "parser")))]
#[cfg(feature = "parser")]
pub fn pretty_read<T>(reader: &mut std::io::Cursor<&[u8]>) -> Result<T>
where
    T: binread::BinRead,
{
    T::read(reader).or_else(|e| {
        let e = Error::from(e);
        let writer = StandardStream::stderr(term::termcolor::ColorChoice::Auto);
        let config = term::Config::default();
        let str = hex::encode(reader.get_ref());
        let file = SimpleFile::new("binary", &str);
        term::emit(&mut writer.lock(), &config, &file, &e.report())?;
        Err(e)
    })
}
