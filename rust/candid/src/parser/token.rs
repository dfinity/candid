use lalrpop_util::ParseError;
use logos::{Lexer, Logos};

#[derive(Logos)]
pub enum Token<'a> {
    #[regex(r"[ \t\n\f]+", logos::skip)]
    #[error]
    Error,
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
    #[regex("[a-zA-Z_][a-zA-Z0-9_]*")]
    Id(&'a str),
    #[regex("\"([^\"\\\\]|\\\\.)*\"")]
    Text(&'a str),
    //Bytes(Vec<u8>),
    //Sign(char),
    #[regex("[+-]?[0-9]+")]
    Number(&'a str),
    #[regex("true|false", |lex| lex.slice().parse())]
    Boolean(bool),
}

pub struct Tokenizer<'input> {
    lex: Lexer<'input, Token<'input>>,
}
impl<'input> Tokenizer<'input> {
    pub fn new(input: &'input str) -> Self {
        let lex = Token::lexer(input);
        Tokenizer { lex }
    }
}

pub type Spanned<Tok, Loc, Error> = Result<(Loc, Tok, Loc), Error>;

pub fn error<'a, E: ToString>(err: E) -> ParseError<usize, Token<'a>, String> {
    ParseError::User {
        error: err.to_string(),
    }
}

impl<'input> Iterator for Tokenizer<'input> {
    type Item = Spanned<Token<'input>, usize, String>;
    fn next(&mut self) -> Option<Self::Item> {
        match self.lex.next() {
            Some(token) => {
                let span = self.lex.span();
                Some(Ok((span.start, token, span.end)))
            }
            None => None,
        }
    }
}
