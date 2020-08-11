use super::types::{Dec, IDLType};

type TupType = Vec<IDLType>;

pub struct Test {
    pub defs: Vec<Dec>,
    pub asserts: Vec<Assert>,
}

pub struct Assert {
    pub assert: Assertion,
    pub desc: Option<String>,
}

pub enum Assertion {
    Decode(Input, TupType),
    NotDecode(Input, TupType),
    Equal(Input, Input, TupType),
    NotEqual(Input, Input, TupType),
}

pub enum Input {
    Text(String),
    Blob(String),
}

impl std::str::FromStr for Test {
    type Err = crate::Error;
    fn from_str(str: &str) -> std::result::Result<Self, Self::Err> {
        let lexer = super::lexer::Lexer::new(str);
        Ok(super::grammar::TestParser::new().parse(lexer)?)
    }
}
