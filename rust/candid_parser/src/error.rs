//! When serializing or deserializing Candid goes wrong.

use candid::types::syntax::{IDLProg, IDLTypes};
use codespan_reporting::diagnostic::Label;
use std::io;
use thiserror::Error;

use crate::{parse_idl_prog, parse_idl_types, token};
use codespan_reporting::{
    diagnostic::Diagnostic,
    files::{Error as ReportError, SimpleFile},
    term::{self, termcolor::StandardStream},
};

pub type Result<T = ()> = std::result::Result<T, Error>;

#[derive(Debug, Error)]
pub enum Error {
    #[error("Candid parser error: {0}")]
    Parse(#[from] token::ParserError),

    #[error(transparent)]
    Custom(#[from] anyhow::Error),

    #[error(transparent)]
    CandidError(#[from] ::candid::Error),
}

impl Error {
    pub fn msg<T: ToString>(msg: T) -> Self {
        Error::Custom(anyhow::anyhow!(msg.to_string()))
    }

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
                    UnrecognizedEof { location, expected } => {
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
            Error::Custom(e) => Diagnostic::error().with_message(e.to_string()),
            Error::CandidError(e) => Diagnostic::error().with_message(e.to_string()),
        }
    }
}

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

impl From<io::Error> for Error {
    fn from(e: io::Error) -> Error {
        Error::msg(format!("io error: {e}"))
    }
}

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

impl From<toml::de::Error> for Error {
    fn from(e: toml::de::Error) -> Error {
        Error::msg(format!("toml error: {e}"))
    }
}

/// Does not work for parsing [IDLProg] and [IDLTypes], use [pretty_parse_idl_prog] and [pretty_parse_idl_types] instead.
pub fn pretty_parse<T>(name: &str, str: &str) -> Result<T>
where
    T: std::str::FromStr<Err = Error>,
{
    str.parse::<T>().or_else(|e| pretty_print_err(name, str, e))
}

pub fn pretty_parse_idl_prog(name: &str, str: &str) -> Result<IDLProg> {
    parse_idl_prog(str).or_else(|e| pretty_print_err(name, str, e))
}

pub fn pretty_parse_idl_types(name: &str, str: &str) -> Result<IDLTypes> {
    parse_idl_types(str).or_else(|e| pretty_print_err(name, str, e))
}

/// Wrap the parser error and pretty print the error message.
/// ```
/// use candid_parser::{pretty_wrap, parse_idl_args};
/// pretty_wrap("parse IDL args", "(42, record {})", parse_idl_args)?;
/// # Ok::<(), candid_parser::Error>(())
/// ```
pub fn pretty_wrap<T>(name: &str, str: &str, f: impl FnOnce(&str) -> Result<T>) -> Result<T> {
    f(str).or_else(|e| pretty_print_err(name, str, e))
}

fn pretty_print_err<T>(name: &str, source: &str, e: Error) -> Result<T> {
    pretty_diagnose(name, source, &e)?;
    Err(e)
}

pub fn pretty_diagnose(file_name: &str, source: &str, e: &Error) -> Result<()> {
    let writer = StandardStream::stderr(term::termcolor::ColorChoice::Auto);
    let config = term::Config::default();
    let file = SimpleFile::new(file_name, source);
    term::emit(&mut writer.lock(), &config, &file, &e.report())?;
    Ok(())
}
