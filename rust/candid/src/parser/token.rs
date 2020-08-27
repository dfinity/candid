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
    //#[regex("\"([^\"\\\\]|\\\\.)*\"", parse_text)]
    #[regex("\"(?:[^\"]|\\\\\")*\"", parse_text)]
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

fn as_text(str: &str) -> Option<String> {
    let mut iter = str.chars();
    let mut result = String::new();
    while let Some(c) = iter.next() {
        match c {
            '\\' => match iter.next()? {
                'n' => result.push('\n'),
                'r' => result.push('\r'),
                't' => result.push('\t'),
                '\\' => result.push('\\'),
                '"' => result.push('"'),
                '\'' => result.push('\''),
                'u' => {
                    iter.next()?;
                    let hex: String = iter.by_ref().take_while(|c| *c != '}').collect();
                    let c = u32::from_str_radix(&hex, 16).ok()?;
                    let c = std::char::from_u32(c)?;
                    result.push(c);
                }
                c if c.is_ascii_hexdigit() => {
                    let mut hex = c.to_string();
                    hex.push(iter.next()?);
                    let byte = u8::from_str_radix(&hex, 16).ok()?;
                    let bytes = unsafe { result.as_mut_vec() };
                    bytes.push(byte);
                }
                _ => return None,
            },
            c => result.push(c),
        }
    }
    Some(result)
}

fn parse_hex(lex: &mut Lexer<Token>) -> Option<String> {
    let num: String = lex.slice()[2..].chars().filter(|c| *c != '_').collect();
    num_bigint::BigInt::parse_bytes(num.as_bytes(), 16).map(|n| n.to_str_radix(10))
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

pub type Spanned<Tok, Loc, Error> = Result<(Loc, Tok, Loc), Error>;

pub fn error<E: ToString>(err: E) -> ParseError<usize, Token, String> {
    ParseError::User {
        error: err.to_string(),
    }
}

impl<'input> Iterator for Tokenizer<'input> {
    type Item = Spanned<Token, usize, String>;
    fn next(&mut self) -> Option<Self::Item> {
        let token = self.lex.next()?;
        match token {
            Token::UnexpectedToken => {
                let span = self.lex.span();
                let msg = format!(
                    "Unknown token {} at {}:{}",
                    self.lex.slice(),
                    span.start,
                    span.end
                );
                Some(Err(msg))
            }
            _ => {
                let span = self.lex.span();
                Some(Ok((span.start, token, span.end)))
            }
        }
    }
}
