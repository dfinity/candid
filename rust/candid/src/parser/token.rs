use lalrpop_util::ParseError;
use logos::{Lexer, Logos};

#[derive(Logos, Debug, Clone, PartialEq, Eq)]
pub enum Token {
    #[regex(r"[ \t\r\n]+", logos::skip)]
    // line comment
    #[regex("//[^\n]*", logos::skip)]
    // block comment (unnested)
    #[regex("/\\*(?:[^*]|\\*[^/])*\\*/", logos::skip)]
    #[error]
    UnexpectedToken,
    #[token("=")]
    Equals,
    #[token(".")]
    Dot,
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
    #[regex("\"([^\"\\\\]|\\\\.)*\"", parse_text)]
    //#[regex("\"(?:[^\"]|\\\\\")*\"", parse_text)]
    Text(String),
    Bytes(Vec<u8>),
    //Sign(char),
    #[regex("[+-]?[0-9][_0-9]*", parse_number)]
    #[regex("0x[0-9a-fA-F][_0-9a-fA-F]*", parse_hex)]
    Number(String),
    #[regex("true|false", |lex| lex.slice().parse())]
    Boolean(bool),
}

impl std::fmt::Display for Token {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(fmt, "{:?}", self)
    }
}

fn parse_text(lex: &mut Lexer<Token>) -> String {
    let text = lex.slice();
    text[1..text.len() - 1].to_string()
}

fn parse_number(lex: &mut Lexer<Token>) -> String {
    lex.slice().chars().filter(|c| *c != '_').collect()
}

fn parse_hex(lex: &mut Lexer<Token>) -> Option<String> {
    let num: String = lex.slice()[2..].chars().filter(|c| *c != '_').collect();
    num_bigint::BigInt::parse_bytes(num.as_bytes(), 16).map(|n| n.to_str_radix(10))
}

pub(crate) type ParserError = ParseError<usize, Token, LexicalError>;

fn next<I>(iter: &mut I, span: &Span, expect: Option<char>) -> Result<char, ParserError>
where
    I: Iterator<Item = char>,
{
    match iter.next() {
        None => Err(error2("Unexpected end of string", span.clone())),
        Some(c) => match expect {
            Some(expect) if c != expect => Err(error2(
                format!("expect {}, but found {}", expect, c),
                span.clone(),
            )),
            _ => Ok(c),
        },
    }
}

pub(crate) fn unescape_text(str: &str, span: &Span, validate: bool) -> Result<String, ParserError> {
    let mut iter = str.chars();
    let mut result = String::new();
    let mut needs_validation = false;
    while let Some(c) = iter.next() {
        match c {
            '\\' => match next(&mut iter, span, None)? {
                'n' => result.push('\n'),
                'r' => result.push('\r'),
                't' => result.push('\t'),
                '\\' => result.push('\\'),
                '"' => result.push('"'),
                '\'' => result.push('\''),
                'u' => {
                    next(&mut iter, &span, Some('{'))?;
                    let mut hex = String::new();
                    loop {
                        match iter.next() {
                            Some(c) if c.is_ascii_hexdigit() => hex.push(c),
                            Some(c) if c == '}' => break,
                            _ => return Err(error2("unknown unicode escape", span.clone())),
                        }
                    }
                    let c =
                        u32::from_str_radix(&hex, 16).map_err(|_| error2(&hex, span.clone()))?;
                    let c = std::char::from_u32(c).ok_or_else(|| {
                        error2(format!("Unicode escape out of range {}", hex), span.clone())
                    })?;
                    result.push(c);
                }
                c if c.is_ascii_hexdigit() => {
                    let mut hex = c.to_string();
                    hex.push(next(&mut iter, &span, None)?);
                    let byte =
                        u8::from_str_radix(&hex, 16).map_err(|_| error2(hex, span.clone()))?;
                    // According to https://webassembly.github.io/spec/core/text/values.html#strings
                    // \hex escape can break utf8 unicode.
                    needs_validation = true;
                    let bytes = unsafe { result.as_mut_vec() };
                    bytes.push(byte);
                }
                c => {
                    return Err(error2(
                        format!("unknown escape character {}", c),
                        span.clone(),
                    ))
                }
            },
            c => result.push(c),
        }
    }
    if validate && needs_validation && String::from_utf8(result.as_bytes().to_vec()).is_err() {
        Err(error2("Not valid unicode text", span.clone()))
    } else {
        Ok(result)
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

#[derive(Clone)]
pub struct Span(pub usize, pub usize);
impl std::fmt::Display for Span {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0 == self.1 && self.1 == 0 {
            write!(fmt, "")
        } else {
            write!(fmt, " at {}:{}", self.0, self.1)
        }
    }
}

pub struct LexicalError {
    err: String,
    span: Span,
}
impl std::fmt::Display for LexicalError {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(fmt, "{}{}", self.err, self.span)
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

pub fn error<E: ToString>(err: E) -> ParseError<usize, Token, LexicalError> {
    ParseError::User {
        error: LexicalError::new(err, Span(0, 0)),
    }
}

pub fn error2<E: ToString>(err: E, span: Span) -> ParseError<usize, Token, LexicalError> {
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
                Some(Err(LexicalError {
                    err,
                    span: Span(span.start, span.end),
                }))
            }
            _ => Some(Ok((span.start, token, span.end))),
        }
    }
}
