use crate::types::Label;
use crate::Result;
use pretty::RcDoc;

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
            pub fn to_doc(&self) -> RcDoc<()> {
                match self {
                    $($name::$variant => RcDoc::text(stringify!($variant).to_lowercase())),*
                }
            }
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

enum_to_doc! {
pub enum FuncMode {
    Oneway,
    Query,
}}

#[derive(Debug, Clone)]
pub struct FuncType {
    pub modes: Vec<FuncMode>,
    pub args: Vec<IDLType>,
    pub rets: Vec<IDLType>,
}

#[derive(Debug, Clone)]
pub struct TypeField {
    pub label: Label,
    pub typ: IDLType,
}

#[derive(Debug)]
pub enum Dec {
    TypD(Binding),
    ImportD(String),
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

impl std::str::FromStr for IDLProg {
    type Err = crate::Error;
    fn from_str(str: &str) -> Result<Self> {
        let lexer = super::token::Tokenizer::new(str);
        Ok(super::grammar::IDLProgParser::new().parse(lexer)?)
    }
}

impl std::str::FromStr for IDLType {
    type Err = crate::Error;
    fn from_str(str: &str) -> Result<Self> {
        let lexer = super::token::Tokenizer::new(str);
        Ok(super::grammar::TypParser::new().parse(lexer)?)
    }
}

impl std::str::FromStr for IDLTypes {
    type Err = crate::Error;
    fn from_str(str: &str) -> Result<Self> {
        let lexer = super::token::Tokenizer::new(str);
        Ok(super::grammar::TypsParser::new().parse(lexer)?)
    }
}
