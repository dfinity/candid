use lalrpop_util::ParseError;
use std::fmt;
use std::iter::Peekable;
use std::str::CharIndices;

pub type Spanned<Tok, Loc, Error> = Result<(Loc, Tok, Loc), Error>;

#[derive(Debug)]
pub enum LexicalError {
    UnknownChar(char),
    OutOfRangeUnicode(u32),
    ParseError(String),
    NonTerminatedString(usize),
    Eof,
}

impl fmt::Display for LexicalError {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LexicalError::Eof => write!(fmt, "Unexpected eof"),
            LexicalError::UnknownChar(c) => write!(fmt, "Unexpected character {}", c),
            LexicalError::ParseError(s) => write!(fmt, "{}", s),
            LexicalError::OutOfRangeUnicode(u) => {
                write!(fmt, "Unicode escape out of range {:x?}", u)
            }
            LexicalError::NonTerminatedString(pos) => {
                write!(fmt, "Unclosed string literal starting at {}", pos)
            }
        }
    }
}

pub fn error<E: ToString>(err: E) -> ParseError<usize, Token, LexicalError> {
    ParseError::User {
        error: LexicalError::ParseError(err.to_string()),
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Token {
    Equals,
    Dot,
    LParen,
    RParen,
    LBrace,
    RBrace,
    Semi,
    Comma,
    Colon,
    Arrow,
    Null,
    Vec,
    Record,
    Variant,
    Func,
    Service,
    Oneway,
    Query,
    Blob,
    Type,
    Import,
    Opt,
    TestEqual,
    NotEqual,
    NotDecode,
    Principal,
    Sign(char),
    Id(String),
    Text(String),
    Bytes(Vec<u8>),
    Number(String),
    Boolean(bool),
}

fn hex_to_char(hex: &str) -> Result<char, LexicalError> {
    let c = u32::from_str_radix(hex, 16).map_err(|_| LexicalError::ParseError(hex.to_owned()))?;
    std::char::from_u32(c).ok_or(LexicalError::OutOfRangeUnicode(c))
}

#[derive(PartialEq)]
enum Radix {
    Decimal,
    Hex,
}

impl fmt::Display for Token {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(fmt, "{:?}", self)
    }
}
pub struct Lexer<'input> {
    input: Peekable<CharIndices<'input>>,
}

impl<'input> Lexer<'input> {
    pub fn new(input: &'input str) -> Lexer<'input> {
        let mut lexer = Lexer {
            input: input.char_indices().peekable(),
        };
        lexer.consume_whitespace();
        lexer
    }

    fn next_char(&mut self) -> Option<(usize, char)> {
        self.input.next()
    }

    fn peek(&mut self) -> Option<(usize, char)> {
        self.input.peek().cloned()
    }

    fn read_next(&mut self) -> Result<char, LexicalError> {
        match self.next_char() {
            Some((_, c)) => Ok(c),
            None => Err(LexicalError::Eof),
        }
    }

    fn consume_next(&mut self, c: char) -> Result<(), LexicalError> {
        let next = self.read_next()?;
        if next == c {
            Ok(())
        } else {
            Err(LexicalError::UnknownChar(next))
        }
    }

    fn consume_whitespace(&mut self) {
        while let Some((_, c)) = self.peek() {
            if c.is_whitespace() {
                self.next_char();
            } else {
                break;
            }
        }
    }

    fn read_num(&mut self, buffer: &mut String, radix: Radix) -> Result<usize, LexicalError> {
        let mut len = 0;
        while let Some((_, c)) = self.peek() {
            if c == '_' {
                len += 1;
                self.next_char();
            } else if (radix == Radix::Decimal && c.is_ascii_digit())
                || (radix == Radix::Hex && c.is_ascii_hexdigit())
            {
                len += 1;
                buffer.push(self.next_char().unwrap().1);
            } else {
                break;
            }
        }
        if len == 0 {
            // Not a single digit was read, this is an error
            Err(LexicalError::Eof)
        } else {
            Ok(len)
        }
    }

    fn read_string_literal(
        &mut self,
        start_position: usize,
        validate: bool,
    ) -> Spanned<Token, usize, LexicalError> {
        let mut result = String::new();
        let mut needs_validation = false;
        let end_position: usize;
        loop {
            match self.next_char() {
                Some((end, '"')) => {
                    end_position = end + 1;
                    break;
                }
                Some((_, '\\')) => match self.read_next()? {
                    'n' => result.push('\n'),
                    'r' => result.push('\r'),
                    't' => result.push('\t'),
                    '\\' => result.push('\\'),
                    '"' => result.push('"'),
                    '\'' => result.push('\''),
                    'u' => {
                        self.consume_next('{')?;
                        let mut hex = String::new();
                        self.read_num(&mut hex, Radix::Hex)?;
                        self.consume_next('}')?;
                        result.push(hex_to_char(&hex)?);
                    }
                    c if c.is_ascii_hexdigit() => {
                        let mut hex = c.to_string();
                        hex.push(self.read_next()?);
                        let byte = u8::from_str_radix(&hex, 16)
                            .map_err(|_| LexicalError::ParseError(hex.to_owned()))?;
                        // According to https://webassembly.github.io/spec/core/text/values.html#strings
                        // \hex escape can break utf8 unicode.
                        needs_validation = true;
                        let bytes = unsafe { result.as_mut_vec() };
                        bytes.push(byte);
                    }
                    c => return Err(LexicalError::UnknownChar(c)),
                },
                Some((_, c)) => result.push(c),
                None => return Err(LexicalError::NonTerminatedString(start_position)),
            }
        }
        if !validate {
            Ok((
                start_position,
                Token::Bytes(result.into_bytes()),
                end_position,
            ))
        } else if needs_validation && String::from_utf8(result.as_bytes().to_vec()).is_err() {
            Err(LexicalError::ParseError(
                "Not valid unicode text".to_owned(),
            ))
        } else {
            Ok((start_position, Token::Text(result), end_position))
        }
    }
}

impl<'input> Iterator for Lexer<'input> {
    type Item = Spanned<Token, usize, LexicalError>;

    fn next(&mut self) -> Option<Self::Item> {
        self.consume_whitespace();
        match self.next_char() {
            Some((i, '(')) => Some(Ok((i, Token::LParen, i + 1))),
            Some((i, ')')) => Some(Ok((i, Token::RParen, i + 1))),
            Some((i, '{')) => Some(Ok((i, Token::LBrace, i + 1))),
            Some((i, '}')) => Some(Ok((i, Token::RBrace, i + 1))),
            Some((i, ';')) => Some(Ok((i, Token::Semi, i + 1))),
            Some((i, ',')) => Some(Ok((i, Token::Comma, i + 1))),
            Some((i, ':')) => Some(Ok((i, Token::Colon, i + 1))),
            Some((i, '.')) => Some(Ok((i, Token::Dot, i + 1))),
            Some((i, '=')) => match self.peek() {
                Some((_, '=')) => {
                    self.next_char();
                    Some(Ok((i, Token::TestEqual, i + 2)))
                }
                _ => Some(Ok((i, Token::Equals, i + 1))),
            },
            Some((i, '!')) => match self.next_char() {
                Some((_, ':')) => Some(Ok((i, Token::NotDecode, i + 2))),
                Some((_, '=')) => Some(Ok((i, Token::NotEqual, i + 2))),
                _ => Some(Err(LexicalError::UnknownChar('!'))),
            },
            Some((i, '+')) => Some(Ok((i, Token::Sign('+'), i + 1))),
            Some((i, '-')) => match self.peek() {
                Some((_, '>')) => {
                    self.next_char();
                    Some(Ok((i, Token::Arrow, i + 2)))
                }
                _ => Some(Ok((i, Token::Sign('-'), i + 1))),
            },
            Some((i, '"')) => Some(self.read_string_literal(i, true)),
            Some((_, '/')) => {
                match self.peek() {
                    Some((_, '/')) => {
                        // line comment
                        self.next_char();
                        while let Some((_, c)) = self.next_char() {
                            if c == '\n' || c == '\r' {
                                break;
                            }
                        }
                        self.next()
                    }
                    Some((_, '*')) => {
                        // multiline comment
                        // TODO handle nested comments
                        self.next_char();
                        let mut seen_star = false;
                        loop {
                            if let Some((_, c)) = self.next_char() {
                                if seen_star && c == '/' {
                                    break;
                                }
                                seen_star = c == '*';
                            } else {
                                return Some(Err(LexicalError::Eof));
                            }
                        }
                        self.next()
                    }
                    _ => Some(Err(LexicalError::UnknownChar('/'))),
                }
            }
            Some((i, c)) if c.is_ascii_digit() => {
                if let Some((_, 'x')) = self.peek() {
                    if c == '0' {
                        // Parse hex number
                        self.next_char();
                        let mut res = String::new();
                        let len = match self.read_num(&mut res, Radix::Hex) {
                            Ok(len) => len,
                            Err(e) => return Some(Err(e)),
                        };
                        let res = match u64::from_str_radix(&res, 16) {
                            Ok(n) => n.to_string(),
                            Err(_) => return Some(Err(LexicalError::ParseError(res))),
                        };
                        Some(Ok((i, Token::Number(res), i + len)))
                    } else {
                        Some(Err(LexicalError::UnknownChar('x')))
                    }
                } else {
                    // Parse decimal number
                    let mut res = c.to_string();
                    let len = self.read_num(&mut res, Radix::Decimal).unwrap_or(0) + 1;
                    Some(Ok((i, Token::Number(res), i + len)))
                }
            }
            Some((i, c)) if c.is_ascii_alphabetic() || c == '_' => {
                // Parse keywords and identifiers
                let mut res = c.to_string();
                while let Some((_, c)) = self.peek() {
                    if c.is_ascii_alphanumeric() || c == '_' {
                        res.push(self.next_char().unwrap().1)
                    } else {
                        break;
                    }
                }
                let tok = match res.as_str() {
                    "true" => Ok((Token::Boolean(true), 4)),
                    "false" => Ok((Token::Boolean(false), 5)),
                    "null" => Ok((Token::Null, 4)),
                    "opt" => Ok((Token::Opt, 3)),
                    "vec" => Ok((Token::Vec, 3)),
                    "record" => Ok((Token::Record, 6)),
                    "variant" => Ok((Token::Variant, 7)),
                    "func" => Ok((Token::Func, 4)),
                    "service" => Ok((Token::Service, 7)),
                    "oneway" => Ok((Token::Oneway, 6)),
                    "query" => Ok((Token::Query, 5)),
                    "blob" => {
                        self.consume_whitespace();
                        match self.peek() {
                            Some((_, c)) if c == '"' => {
                                self.next_char();
                                return Some(self.read_string_literal(i, false));
                            }
                            _ => Ok((Token::Blob, 4)),
                        }
                    }
                    "type" => Ok((Token::Type, 4)),
                    "import" => Ok((Token::Import, 6)),
                    "principal" => Ok((Token::Principal, 9)),
                    id => Ok((Token::Id(id.to_string()), id.len())),
                };
                Some(tok.map(|(token, len)| (i, token, i + len)))
            }
            Some((_, c)) => Some(Err(LexicalError::ParseError(c.to_string()))),
            None => None,
        }
    }
}
