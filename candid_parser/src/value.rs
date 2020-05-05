//use candid_info::types::{Field, Type};
use std::fmt;
//use std::ops::Deref;

#[derive(Debug, PartialEq, Clone)]
pub enum IDLValue {
    Bool(bool),
    Null,
    Text(String),
    Int(i64),
    Nat(u64),
    None,
    Opt(Box<IDLValue>),
    Vec(Vec<IDLValue>),
    Record(Vec<IDLField>),
    Variant(Box<IDLField>),
}

#[derive(Debug, PartialEq, Clone)]
pub struct IDLField {
    pub id: u32,
    pub val: IDLValue,
}

#[derive(Debug, PartialEq, Clone)]
pub struct IDLArgs {
    pub args: Vec<IDLValue>,
}

pub type ParserError =
    lalrpop_util::ParseError<usize, crate::lexer::Token, crate::lexer::LexicalError>;

/*
impl IDLArgs {
    pub fn new(args: &[IDLValue]) -> Self {
        IDLArgs {
            args: args.to_owned(),
        }
    }
    pub fn to_bytes(&self) -> crate::Result<Vec<u8>> {
        let mut idl = crate::ser::IDLBuilder::new();
        for v in self.args.iter() {
            idl.value_arg(v)?;
        }
        idl.serialize_to_vec()
    }
    pub fn from_bytes(bytes: &[u8]) -> crate::Result<Self> {
        let mut de = crate::de::IDLDeserialize::new(bytes);
        let mut args = Vec::new();
        while !de.is_done() {
            let v = de.get_value::<IDLValue>()?;
            args.push(v);
        }
        de.done()?;
        Ok(IDLArgs { args })
    }
}
*/
impl std::str::FromStr for IDLArgs {
    type Err = ParserError;
    fn from_str(str: &str) -> Result<Self, Self::Err> {
        let lexer = crate::lexer::Lexer::new(str);
        Ok(crate::grammar::ArgsParser::new().parse(lexer)?)
    }
}

impl fmt::Display for IDLArgs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        let len = self.args.len();
        for i in 0..len {
            write!(f, "{}", self.args[i])?;
            if i < len - 1 {
                write!(f, ", ")?;
            }
        }
        write!(f, ")")
    }
}

impl fmt::Display for IDLValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            IDLValue::Null => write!(f, "null"),
            IDLValue::Bool(b) => write!(f, "{}", b),
            IDLValue::Int(i) => {
                if i >= 0 {
                    write!(f, "+{}", i)
                } else {
                    write!(f, "{}", i)
                }
            }
            IDLValue::Nat(n) => write!(f, "{}", n),
            IDLValue::Text(ref s) => write!(f, "\"{}\"", s),
            IDLValue::None => write!(f, "none"),
            IDLValue::Opt(ref v) => write!(f, "opt {}", v),
            IDLValue::Vec(ref vec) => {
                write!(f, "vec {{ ")?;
                for e in vec.iter() {
                    write!(f, "{}; ", e)?;
                }
                write!(f, "}}")
            }
            IDLValue::Record(ref fs) => {
                write!(f, "record {{ ")?;
                for e in fs.iter() {
                    write!(f, "{}; ", e)?;
                }
                write!(f, "}}")
            }
            IDLValue::Variant(ref v) => write!(f, "variant {{ {} }}", v),
        }
    }
}

impl fmt::Display for IDLField {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} = {}", self.id, self.val)
    }
}
