use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::Result;
use candid::types::{FuncMode, Label};

#[derive(Debug, Clone)]
pub enum IDLType {
    PrimT(PrimType),
    VarT(String),
    FuncT(FuncType),
    OptT(Box<IDLType>),
    VecT(Box<IDLType>),
    RecordT(Vec<TypeField>),
    VariantT(Vec<TypeField>),
    ServT(Vec<Binding>),
    ClassT(Vec<IDLArgType>, Box<IDLType>),
    PrincipalT,
}

#[derive(Debug, Clone)]
pub struct IDLTypes {
    pub args: Vec<IDLType>,
}

macro_rules! enum_to_doc {
    (pub enum $name:ident {
        $($variant:ident),*,
    }) => {
        #[derive(Debug, Clone, PartialEq, Eq, Hash)]
        pub enum $name {
            $($variant),*
        }
        impl $name {
            pub fn str_to_enum(str: &str) -> Option<Self> {
                $(if str == stringify!($variant).to_lowercase() {
                    return Some($name::$variant);
                });*
                return None;
            }
        }
    };
}

enum_to_doc! {
pub enum PrimType {
    Nat,
    Nat8,
    Nat16,
    Nat32,
    Nat64,
    Int,
    Int8,
    Int16,
    Int32,
    Int64,
    Float32,
    Float64,
    Bool,
    Text,
    Null,
    Reserved,
    Empty,
}}

#[derive(Debug, Clone)]
pub struct FuncType {
    pub modes: Vec<FuncMode>,
    pub args: Vec<IDLArgType>,
    pub rets: Vec<IDLType>,
}

#[derive(Debug, Clone)]
pub struct IDLArgType {
    pub typ: IDLType,
    pub name: Option<String>,
}

impl IDLArgType {
    pub fn new(typ: IDLType) -> Self {
        Self { typ, name: None }
    }

    /// Create a new IDLArgType with a name.
    /// If the name is an `u32` number, we set it to None
    /// as we don't want to use it as a arg name.
    pub fn new_with_name(typ: IDLType, name: String) -> Self {
        let name = if name.parse::<u32>().is_ok() {
            None
        } else {
            Some(name)
        };
        Self { typ, name }
    }
}

#[derive(Debug, Clone)]
pub struct TypeField {
    pub label: Label,
    pub typ: IDLType,
}

#[derive(Debug)]
pub struct Dec {
    pub doc_comment: Option<Vec<String>>,
    pub inner: DecInner,
}

#[derive(Debug)]
pub enum DecInner {
    TypD(Binding),
    ImportType(String),
    ImportServ(String),
}

#[derive(Debug, Clone)]
pub struct Binding {
    pub id: String,
    pub typ: IDLType,
}

#[derive(Debug)]
pub struct IDLProg {
    pub decs: Vec<Dec>,
    pub actor: Option<IDLType>,
}

#[derive(Debug)]
pub struct IDLInitArgs {
    pub decs: Vec<Dec>,
    pub args: Vec<IDLArgType>,
}

impl std::str::FromStr for IDLProg {
    type Err = crate::Error;
    fn from_str(str: &str) -> Result<Self> {
        let trivia: super::token::TriviaMap = Rc::new(RefCell::new(HashMap::new()));
        let lexer = super::token::Tokenizer::new_with_trivia(str, trivia.clone());
        let res = super::grammar::IDLProgParser::new().parse(Some(&trivia.clone()), lexer)?;
        println!("{res:?}");
        Ok(res)
    }
}
impl std::str::FromStr for IDLInitArgs {
    type Err = crate::Error;
    fn from_str(str: &str) -> Result<Self> {
        let lexer = super::token::Tokenizer::new(str);
        Ok(super::grammar::IDLInitArgsParser::new().parse(None, lexer)?)
    }
}

impl std::str::FromStr for IDLType {
    type Err = crate::Error;
    fn from_str(str: &str) -> Result<Self> {
        let lexer = super::token::Tokenizer::new(str);
        Ok(super::grammar::TypParser::new().parse(None, lexer)?)
    }
}

impl std::str::FromStr for IDLTypes {
    type Err = crate::Error;
    fn from_str(str: &str) -> Result<Self> {
        let lexer = super::token::Tokenizer::new(str);
        Ok(super::grammar::TypsParser::new().parse(None, lexer)?)
    }
}
