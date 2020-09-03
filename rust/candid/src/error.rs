//! `candid::Result<T> = Result<T, candid::Error>>`

use serde::{de, ser};

use crate::parser::token;
use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::files::SimpleFile;
use codespan_reporting::term::{self, termcolor::StandardStream};
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
                let label = match e {
                    User { error } => {
                        Label::primary((), error.span.clone()).with_message(&error.err)
                    }
                    InvalidToken { location } => {
                        Label::primary((), *location..location + 1).with_message("Invalid token")
                    }
                    UnrecognizedEOF { location, expected } => {
                        diag = diag.with_notes(report_expected(&expected));
                        Label::primary((), *location..location + 1).with_message("Unexpected EOF")
                    }
                    UnrecognizedToken { token, expected } => {
                        diag = diag.with_notes(report_expected(&expected));
                        Label::primary((), token.0..token.2).with_message("Unexpected token")
                    }
                    ExtraToken { token } => {
                        Label::primary((), token.0..token.2).with_message("Extra token")
                    }
                };
                diag.with_labels(vec![label])
            }
            Error::Deserialize(e, _) => Diagnostic::error().with_message(e),
            Error::Custom(e) => Diagnostic::error().with_message(e),
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
