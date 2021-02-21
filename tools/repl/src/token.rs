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
    #[token(".")]
    Dot,
    #[token(",")]
    Comma,
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
    Args(Vec<String>),
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
            Token::LParen => {
                let mut nesting = 1;
                let mut res = Vec::new();
                let mut arg = String::new();
                loop {
                    match self.lex.next() {
                        Some(Token::LParen) => {
                            nesting += 1;
                            arg.push_str(self.lex.slice());
                        }
                        Some(Token::RParen) => {
                            nesting -= 1;
                            if nesting == 0 {
                                if !arg.is_empty() {
                                    res.push(arg);
                                }
                                break;
                            } else {
                                arg.push_str(self.lex.slice());
                            }
                        }
                        // TODO fix comma in string
                        Some(Token::Comma) if nesting == 1 => {
                            res.push(arg.clone());
                            arg.clear();
                        }
                        Some(_) => arg.push_str(self.lex.slice()),
                        None => {
                            res.push(arg);
                            break;
                        }
                    }
                }
                Some((span.start, Token::Args(res), self.lex.span().end))
            }
            _ => Some((span.start, token, span.end)),
        }
    }
}
