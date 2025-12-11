use std::{cell::RefCell, collections::HashMap, mem, rc::Rc};

use lalrpop_util::ParseError;
use logos::{Lexer, Logos};

const LINE_COMMENT_PREFIX: &str = "//";

#[derive(Logos, Debug, Clone, PartialEq, Eq, Ord, PartialOrd)]
#[logos(skip r"[ \t\r\n]+")]
pub enum Token {
    #[regex(r"//[^\n]*")] // must start with `LINE_COMMENT_PREFIX`
    LineComment,
    #[token("/*")]
    StartComment,
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
    #[token("composite_query")]
    CompositeQuery,
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
    #[regex("[0-9]+(\\.[0-9]*)?[eE][+-]?[0-9]+", parse_number)]
    Float(String),
    #[regex("true|false", |lex| lex.slice().parse().map_err(|_| ()))]
    Boolean(bool),
}

#[derive(Logos, Debug, Clone, PartialEq, Eq)]
enum Comment {
    #[token("*/")]
    End,
    #[token("/*")]
    Start,
}

#[derive(Logos, Debug, Clone, PartialEq, Eq)]
#[allow(clippy::enum_variant_names)]
enum Text {
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
        write!(fmt, "{self:?}")
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

fn parse_doc_comment(lex: &Lexer<Token>) -> String {
    lex.slice()
        .trim_start_matches(LINE_COMMENT_PREFIX)
        .trim()
        .to_string()
}

pub type TriviaMap = Rc<RefCell<HashMap<usize, Vec<String>>>>;

pub struct Tokenizer<'input> {
    lex: Lexer<'input, Token>,
    comment_buffer: Vec<String>,
    trivia: Option<TriviaMap>,
    last_comment_end: Option<usize>,
    last_token_line_end: Option<usize>,
}

impl<'input> Tokenizer<'input> {
    pub fn new(input: &'input str) -> Self {
        let lex = Token::lexer(input);
        Tokenizer {
            lex,
            comment_buffer: vec![],
            trivia: None,
            last_comment_end: None,
            last_token_line_end: None,
        }
    }

    pub fn new_with_trivia(input: &'input str, trivia: TriviaMap) -> Self {
        let lex = Token::lexer(input);
        Tokenizer {
            lex,
            comment_buffer: vec![],
            trivia: Some(trivia),
            last_comment_end: None,
            last_token_line_end: None,
        }
    }

    /// Count newlines between two positions in the source
    fn count_newlines_between(&self, start: usize, end: usize) -> usize {
        let source = self.lex.source();
        if start < end && end <= source.len() {
            source[start..end].chars().filter(|&c| c == '\n').count()
        } else {
            0
        }
    }

    /// Check if there's a blank line (or more) between the end of the last comment
    /// and the start of the current token
    fn has_blank_line_before_token(&self, token_start: usize) -> bool {
        self.last_comment_end
            .map(|end| self.count_newlines_between(end, token_start) >= 2)
            .unwrap_or(false)
    }

    /// Check if the comment is on the same line as the previous token (inline comment)
    fn is_inline_comment(&self, comment_start: usize) -> bool {
        self.last_token_line_end
            .map(|line_end| comment_start <= line_end)
            .unwrap_or(false)
    }

    /// Find the end of the line containing the given position
    fn find_line_end(&self, pos: usize) -> usize {
        let source = self.lex.source();
        source[pos..]
            .find('\n')
            .map(|offset| pos + offset)
            .unwrap_or(source.len())
    }
}

pub type Span = std::ops::Range<usize>;

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

pub type ParserError = ParseError<usize, Token, LexicalError>;
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

impl Iterator for Tokenizer<'_> {
    type Item = Result<(usize, Token, usize), LexicalError>;
    fn next(&mut self) -> Option<Self::Item> {
        let token = self.lex.next()?;
        let span = self.lex.span();
        match token {
            Err(_) => {
                let err = format!("Unknown token {}", self.lex.slice());
                Some(Err(LexicalError::new(err, span)))
            }
            Ok(Token::LineComment) => {
                let content = parse_doc_comment(&self.lex);
                if self.trivia.is_some() && !self.is_inline_comment(span.start) {
                    if self.has_blank_line_before_token(span.start) {
                        self.comment_buffer.clear();
                    }
                    self.comment_buffer.push(content.to_string());
                    self.last_comment_end = Some(span.end);
                }
                self.next()
            }
            Ok(Token::StartComment) => {
                let mut lex = self.lex.to_owned().morph::<Comment>();
                let mut nesting = 1;
                loop {
                    match lex.next() {
                        Some(Err(_)) => continue,
                        Some(Ok(Comment::End)) => {
                            nesting -= 1;
                            if nesting == 0 {
                                break;
                            }
                        }
                        Some(Ok(Comment::Start)) => nesting += 1,
                        None => {
                            return Some(Err(LexicalError::new(
                                "Unclosed comment",
                                span.start..lex.span().end,
                            )))
                        }
                    }
                }
                self.lex = lex.morph::<Token>();
                // Update last_comment_end to skip over the block comment
                // This prevents block comments from breaking doc comment continuity
                self.last_comment_end = Some(self.lex.span().start);
                self.next()
            }
            Ok(Token::StartString) => {
                let mut result = String::new();
                let mut lex = self.lex.to_owned().morph::<Text>();
                loop {
                    use self::Text::*;
                    match lex.next() {
                        Some(Ok(Text)) => result += lex.slice(),
                        Some(Ok(EscapeCharacter)) => match lex.slice().chars().nth(1).unwrap() {
                            'n' => result.push('\n'),
                            'r' => result.push('\r'),
                            't' => result.push('\t'),
                            '\\' => result.push('\\'),
                            '"' => result.push('"'),
                            '\'' => result.push('\''),
                            c => {
                                return Some(Err(LexicalError::new(
                                    format!("Unknown escape character {c}"),
                                    lex.span(),
                                )))
                            }
                        },
                        Some(Ok(Codepoint)) => {
                            let slice = lex.slice();
                            let hex = slice[3..slice.len() - 1].replace('_', "");
                            match u32::from_str_radix(&hex, 16)
                                .map_err(|_| {
                                    LexicalError::new("Not a valid hex escape", lex.span())
                                })
                                .and_then(|c| {
                                    std::char::from_u32(c).ok_or_else(|| {
                                        LexicalError::new(
                                            format!("Unicode escape out of range {hex}"),
                                            lex.span(),
                                        )
                                    })
                                }) {
                                Ok(c) => result.push(c),
                                Err(e) => return Some(Err(e)),
                            }
                        }
                        Some(Ok(Byte)) => {
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
                        Some(Ok(EndString)) => break,
                        Some(Err(_)) => {
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
            Ok(token) => {
                // Check for blank line before getting mutable reference
                let has_blank_line = self.has_blank_line_before_token(span.start);

                if let Some(trivia) = &mut self.trivia {
                    if !self.comment_buffer.is_empty() {
                        if !has_blank_line {
                            let content: Vec<String> = mem::take(&mut self.comment_buffer);
                            trivia.borrow_mut().insert(span.start, content);
                        } else {
                            self.comment_buffer.clear();
                        }
                    }
                    self.last_comment_end = None;
                }
                self.last_token_line_end = Some(self.find_line_end(span.end));

                Some(Ok((span.start, token, span.end)))
            }
        }
    }
}
