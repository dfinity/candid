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
            LexicalError::ParseError(s) => write!(fmt, "Error parsing {}", s),
            LexicalError::OutOfRangeUnicode(u) => {
                write!(fmt, "Unicode escape out of range {:x?}", u)
            }
            LexicalError::NonTerminatedString(pos) => {
                write!(fmt, "Unclosed string literal starting at {}", pos)
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Token {
    Equals,
    Dot,
    Plus,
    Minus,
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
    None,
    Opt,
    Id(String),
    Text(String),
    Number(String),
    Boolean(bool),
}

pub struct TmpIDLField {
    pub has_id: bool,
    pub inner: crate::value::IDLField,
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
    ) -> Spanned<Token, usize, LexicalError> {
        let mut result = String::new();
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
                        result.push(hex_to_char(&hex)?);
                    }
                    c => return Err(LexicalError::UnknownChar(c)),
                },
                Some((_, c)) => result.push(c),
                None => return Err(LexicalError::NonTerminatedString(start_position)),
            }
        }
        Ok((start_position, Token::Text(result), end_position))
    }
}

impl<'input> Iterator for Lexer<'input> {
    type Item = Spanned<Token, usize, LexicalError>;

    fn next(&mut self) -> Option<Self::Item> {
        let token = match self.next_char() {
            Some((i, '(')) => Some(Ok((i, Token::LParen, i + 1))),
            Some((i, ')')) => Some(Ok((i, Token::RParen, i + 1))),
            Some((i, '{')) => Some(Ok((i, Token::LBrace, i + 1))),
            Some((i, '}')) => Some(Ok((i, Token::RBrace, i + 1))),
            Some((i, ';')) => Some(Ok((i, Token::Semi, i + 1))),
            Some((i, ',')) => Some(Ok((i, Token::Comma, i + 1))),
            Some((i, ':')) => Some(Ok((i, Token::Colon, i + 1))),
            Some((i, '=')) => Some(Ok((i, Token::Equals, i + 1))),
            Some((i, '+')) => Some(Ok((i, Token::Plus, i + 1))),
            Some((i, '-')) => match self.peek() {
                Some((_, '>')) => {
                    self.next_char();
                    Some(Ok((i, Token::Arrow, i + 2)))
                }
                _ => Some(Ok((i, Token::Minus, i + 1))),
            },
            Some((i, '"')) => Some(self.read_string_literal(i)),
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
                        return Some(Err(LexicalError::UnknownChar('x')));
                    }
                } else {
                    // Parse decimal number
                    let mut res = c.to_string();
                    let len = self.read_num(&mut res, Radix::Decimal).unwrap_or(0) + 1;
                    Some(Ok((i, Token::Number(res), i + len)))
                }
            }
            Some((i, c)) if c.is_ascii_alphabetic() => {
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
                    "none" => Ok((Token::None, 4)),
                    "null" => Ok((Token::Null, 4)),
                    "opt" => Ok((Token::Opt, 3)),
                    "vec" => Ok((Token::Vec, 3)),
                    "record" => Ok((Token::Record, 6)),
                    "variant" => Ok((Token::Variant, 7)),
                    "func" => Ok((Token::Func, 4)),
                    "service" => Ok((Token::Service, 7)),
                    "oneway" => Ok((Token::Oneway, 6)),
                    "query" => Ok((Token::Query, 5)),
                    "blob" => Ok((Token::Blob, 4)),
                    "type" => Ok((Token::Type, 4)),
                    "import" => Ok((Token::Import, 6)),
                    id => Ok((Token::Id(id.to_string()), id.len())),
                };
                Some(tok.map(|(token, len)| (i, token, i + len)))
            }
            Some((_, c)) => Some(Err(LexicalError::ParseError(c.to_string()))),
            None => None,
        };
        self.consume_whitespace();
        token
    }
}
