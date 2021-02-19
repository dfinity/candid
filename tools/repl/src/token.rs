use candid::parser::value::IDLValue;
use logos::{Lexer, Logos};

#[derive(Logos, Debug, PartialEq, Clone)]
pub enum Token {
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
    #[token("call")]
    Call,
    #[token("let")]
    Let,
    #[token("import")]
    Import,
    #[token("config")]
    Config,
    #[token("\"")]
    StartString,
    Text(String),
    Candid(IDLValue),
    #[regex("[a-zA-Z_][a-zA-Z0-9_]*", |lex| lex.slice().to_string())]
    Id(String),
}

#[derive(Logos, Debug, PartialEq, Clone)]
enum Text {
    #[error]
    Error,
    #[regex(r#"[^\\"]+"#)]
    Text,
    #[regex(r"\\.")]
    EscapeCharacter,
    #[token("\"")]
    EndString,
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
        match token {
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
                            _ => {
                                return Some((
                                    lex.span().start,
                                    Token::UnexpectedToken,
                                    lex.span().end,
                                ))
                            }
                        },
                        Some(EndString) => break,
                        Some(Error) | None => {
                            return Some((lex.span().start, Token::UnexpectedToken, lex.span().end))
                        }
                    }
                }
                self.lex = lex.morph::<Token>();
                Some((span.start, Token::Text(result), self.lex.span().end))
            }
            _ => Some((span.start, token, span.end)),
        }
    }
}
