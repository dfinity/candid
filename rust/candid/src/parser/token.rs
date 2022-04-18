use lalrpop_util::ParseError;
use logos::{Lexer, Logos};

#[derive(Logos, Debug, Clone, PartialEq, Eq, Ord, PartialOrd)]
pub enum Token {
    #[regex(r"[ \t\r\n]+", logos::skip)]
    // line comment
    #[regex("//[^\n]*", logos::skip)]
    #[token("/*")]
    StartComment,
    #[error]
    UnexpectedToken,
    #[token("=")]
    Equals,
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,
    #[token(";")]
    Semi,
    #[token(",")]
    Comma,
    #[token(".", priority = 10)]
    Dot,
    #[token(":")]
    Colon,
    #[token("->")]
    Arrow,
    #[token("null")]
    Null,
    #[token("vec")]
    Vec,
    #[token("record")]
    Record,
    #[token("variant")]
    Variant,
    #[token("func")]
    Func,
    #[token("service")]
    Service,
    #[token("oneway")]
    Oneway,
    #[token("query")]
    Query,
    #[token("blob")]
    Blob,
    #[token("type")]
    Type,
    #[token("import")]
    Import,
    #[token("opt")]
    Opt,
    #[token("==")]
    TestEqual,
    #[token("!=")]
    NotEqual,
    #[token("!:")]
    NotDecode,
    #[token("principal")]
    Principal,
    #[regex("[a-zA-Z_][a-zA-Z0-9_]*", |lex| lex.slice().to_string())]
    Id(String),
    #[token("\"")]
    StartString,
    // This token is not derived. Stores the unescaped string
    Text(String),
    #[regex("[+-]", |lex| lex.slice().chars().next())]
    Sign(char),
    #[regex("[0-9][_0-9]*", parse_number)]
    Decimal(String),
    #[regex("0[xX][0-9a-fA-F][_0-9a-fA-F]*", parse_number)]
    Hex(String),
    #[regex("[0-9]*\\.[0-9]*", parse_number)]
    #[regex("[0-9]*(\\.[0-9]*)?[eE][+-]?[0-9]+", parse_number)]
    Float(String),
    #[regex("true|false", |lex| lex.slice().parse())]
    Boolean(bool),
}

#[derive(Logos, Debug, Clone, PartialEq, Eq)]
enum Comment {
    #[error]
    Skip,
    #[token("*/")]
    End,
    #[token("/*")]
    Start,
}

#[allow(clippy::enum_variant_names)]
#[derive(Logos, Debug, Clone, PartialEq, Eq)]
enum Text {
    #[error]
    Error,
    #[regex(r#"[^\\"]+"#)]
    Text,
    #[regex(r"\\.")]
    EscapeCharacter,
    #[regex(r"\\u\{[0-9a-fA-F][_0-9a-fA-F]*\}")]
    Codepoint,
    #[regex(r"\\[0-9a-fA-F][0-9a-fA-F]")]
    Byte,
    #[token("\"")]
    EndString,
}

impl std::fmt::Display for Token {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(fmt, "{:?}", self)
    }
}

fn parse_number(lex: &mut Lexer<Token>) -> String {
    let iter = lex.slice().chars().filter(|c| *c != '_');
    if lex.slice().starts_with("0x") {
        iter.skip(2).collect()
    } else {
        iter.collect()
    }
}

pub struct Tokenizer<'input> {
    lex: Lexer<'input, Token>,
}
impl<'input> Tokenizer<'input> {
    pub fn new(input: &'input str) -> Self {
        let lex = Token::lexer(input);
        Tokenizer { lex }
    }
}

pub type Span = std::ops::Range<usize>;
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Spanned<T> {
    pub span: Span,
    pub value: T,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LexicalError {
    pub err: String,
    pub span: Span,
}
impl std::fmt::Display for LexicalError {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.span.start == 0 && self.span.end == 0 {
            write!(fmt, "{}", self.err)
        } else {
            write!(fmt, "{} at {:?}", self.err, self.span)
        }
    }
}
impl LexicalError {
    fn new<E: ToString>(err: E, span: Span) -> Self {
        LexicalError {
            err: err.to_string(),
            span,
        }
    }
}

pub(crate) type ParserError = ParseError<usize, Token, LexicalError>;
pub fn error<E: ToString>(err: E) -> ParserError {
    ParseError::User {
        error: LexicalError::new(err, 0..0),
    }
}
pub fn error2<E: ToString>(err: E, span: Span) -> ParserError {
    ParseError::User {
        error: LexicalError::new(err, span),
    }
}

impl<'input> Iterator for Tokenizer<'input> {
    type Item = Result<(usize, Token, usize), LexicalError>;
    fn next(&mut self) -> Option<Self::Item> {
        let token = self.lex.next()?;
        let span = self.lex.span();
        match token {
            Token::UnexpectedToken => {
                let err = format!("Unknown token {}", self.lex.slice());
                Some(Err(LexicalError::new(err, span)))
            }
            Token::StartComment => {
                let mut lex = self.lex.to_owned().morph::<Comment>();
                let mut nesting = 1;
                loop {
                    match lex.next() {
                        Some(Comment::Skip) => continue,
                        Some(Comment::End) => {
                            nesting -= 1;
                            if nesting == 0 {
                                break;
                            }
                        }
                        Some(Comment::Start) => nesting += 1,
                        None => {
                            return Some(Err(LexicalError::new(
                                "Unclosed comment",
                                span.start..lex.span().end,
                            )))
                        }
                    }
                }
                self.lex = lex.morph::<Token>();
                self.next()
            }
            Token::StartString => {
                let mut result = String::new();
                let mut lex = self.lex.to_owned().morph::<Text>();
                loop {
                    use self::Text::*;
                    match lex.next() {
                        Some(Text) => result += lex.slice(),
                        Some(EscapeCharacter) => match lex.slice().chars().nth(1).unwrap() {
                            'n' => result.push('\n'),
                            'r' => result.push('\r'),
                            't' => result.push('\t'),
                            '\\' => result.push('\\'),
                            '"' => result.push('"'),
                            '\'' => result.push('\''),
                            c => {
                                return Some(Err(LexicalError::new(
                                    format!("Unknown escape character {}", c),
                                    lex.span(),
                                )))
                            }
                        },
                        Some(Codepoint) => {
                            let slice = lex.slice();
                            let hex = slice[3..slice.len() - 1].replace('_', "");
                            match u32::from_str_radix(&hex, 16)
                                .map_err(|_| {
                                    LexicalError::new("Not a valid hex escape", lex.span())
                                })
                                .and_then(|c| {
                                    std::char::from_u32(c).ok_or_else(|| {
                                        LexicalError::new(
                                            format!("Unicode escape out of range {}", hex),
                                            lex.span(),
                                        )
                                    })
                                }) {
                                Ok(c) => result.push(c),
                                Err(e) => return Some(Err(e)),
                            }
                        }
                        Some(Byte) => {
                            let hex = &lex.slice()[1..];
                            match u8::from_str_radix(hex, 16) {
                                Ok(byte) => {
                                    // According to https://webassembly.github.io/spec/core/text/values.html#strings
                                    // \xx escape can break utf8 unicode.
                                    let bytes = unsafe { result.as_mut_vec() };
                                    bytes.push(byte);
                                }
                                Err(_) => {
                                    return Some(Err(LexicalError::new(
                                        "Not a valid hex escape",
                                        lex.span(),
                                    )))
                                }
                            }
                        }
                        Some(EndString) => break,
                        Some(Error) => {
                            return Some(Err(LexicalError::new(
                                format!("Unexpected string {}", lex.slice()),
                                lex.span(),
                            )))
                        }
                        None => {
                            return Some(Err(LexicalError::new(
                                "Unclosed string",
                                span.start..lex.span().end,
                            )))
                        }
                    }
                }
                self.lex = lex.morph::<Token>();
                Some(Ok((span.start, Token::Text(result), self.lex.span().end)))
            }
            _ => Some(Ok((span.start, token, span.end))),
        }
    }
}
