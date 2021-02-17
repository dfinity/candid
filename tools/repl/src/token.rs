use logos::{Lexer, Logos};

#[derive(Logos, Debug, PartialEq)]
pub enum Token<'input> {
    #[regex(r"[ \t\r\n]+", logos::skip)]
    #[regex("//[^\n]*", logos::skip)]    
    #[error]
    UnexpectedToken,
    #[token("=")]
    Equals,
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token(",")]
    Comma,
    #[token(".")]
    Dot,
    #[regex("[a-zA-Z_][a-zA-Z0-9_]*", |lex| lex.slice())]
    Id(&'input str),
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

impl<'input> Iterator for Tokenizer<'input> {
    type Item = (usize, Token, usize);
    fn next(&mut self) -> Option<Self::Item> {
        let token = self.lex.next()?;
        let span = self.lex.span();
        Some((span.start, token, span.end))
    }
}

