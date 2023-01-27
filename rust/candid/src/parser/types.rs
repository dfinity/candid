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
    ClassT(Vec<IDLType>, Box<IDLType>),
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
            pub(crate) fn to_doc(&self) -> RcDoc<()> {
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

impl FuncType {
    pub fn is_query(&self) -> bool {
        for m in self.modes.iter() {
            if let FuncMode::Query = m {
                return true;
            }
        }
        false
    }
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

// Pretty printing

pub trait ToDoc {
    fn to_doc(&self) -> RcDoc<()>;
}

pub fn to_pretty<T>(doc: &T, width: usize) -> String
where
    T: ToDoc,
{
    let mut w = Vec::new();
    doc.to_doc().render(width, &mut w).unwrap();
    String::from_utf8(w).unwrap()
}

impl ToDoc for IDLProg {
    fn to_doc(&self) -> RcDoc<()> {
        let doc = RcDoc::concat(
            self.decs
                .iter()
                .map(|d| d.to_doc().append(RcDoc::text(";").append(RcDoc::line()))),
        );
        if self.actor.is_some() {
            let actor = self.actor.as_ref().unwrap();
            let doc = doc.append(RcDoc::text("service : "));
            match actor {
                IDLType::VarT(ref var) => doc.append(RcDoc::text(var.to_string())),
                IDLType::ServT(ref meths) => doc.append(meths_to_doc(meths)),
                _ => unreachable!(),
            }
        } else {
            doc
        }
    }
}

impl ToDoc for Dec {
    fn to_doc(&self) -> RcDoc<()> {
        match *self {
            Dec::TypD(ref b) => RcDoc::text("type ").append(b.to_doc()),
            Dec::ImportD(ref file) => RcDoc::text(format!("import \"{file}\"")),
        }
    }
}

impl ToDoc for Binding {
    fn to_doc(&self) -> RcDoc<()> {
        RcDoc::text(format!("{} =", self.id))
            .append(RcDoc::space())
            .append(self.typ.to_doc())
            .nest(2)
            .group()
    }
}

impl ToDoc for IDLType {
    fn to_doc(&self) -> RcDoc<()> {
        match self {
            IDLType::PrimT(p) => p.to_doc(),
            IDLType::VarT(var) => RcDoc::text(var),
            IDLType::FuncT(func) => RcDoc::text("func")
                .append(RcDoc::space())
                .append(func.to_doc()),
            IDLType::OptT(ref t) => RcDoc::text("opt").append(RcDoc::space()).append(t.to_doc()),
            IDLType::VecT(ref t) => RcDoc::text("vec").append(RcDoc::space()).append(t.to_doc()),
            IDLType::RecordT(ref fs) => RcDoc::text("record ").append(fields_to_doc(fs)),
            IDLType::VariantT(ref fs) => RcDoc::text("variant ").append(fields_to_doc(fs)),
            IDLType::ServT(ref serv) => RcDoc::text("service ").append(meths_to_doc(serv)),
            IDLType::ClassT(_, _) => unreachable!(),
            IDLType::PrincipalT => RcDoc::text("principal"),
        }
        .nest(2)
        .group()
    }
}

impl ToDoc for FuncType {
    fn to_doc(&self) -> RcDoc<()> {
        args_to_doc(&self.args)
            .append(RcDoc::space())
            .append(RcDoc::text("-> "))
            .append(args_to_doc(&self.rets))
            .append(RcDoc::concat(
                self.modes.iter().map(|m| RcDoc::space().append(m.to_doc())),
            ))
    }
}

impl ToDoc for TypeField {
    fn to_doc(&self) -> RcDoc<()> {
        let colon = RcDoc::text(":").append(RcDoc::space());
        let doc = match &self.label {
            Label::Id(n) => RcDoc::as_string(n).append(colon),
            Label::Named(name) => RcDoc::text(name).append(colon),
            Label::Unnamed(_) => RcDoc::nil(),
        };
        doc.append(self.typ.to_doc()).nest(2).group()
    }
}

fn fields_to_doc(fields: &[TypeField]) -> RcDoc<()> {
    RcDoc::text("{")
        .append(
            RcDoc::concat(
                fields
                    .iter()
                    .map(|f| RcDoc::space().append(f.to_doc()).append(RcDoc::text(";"))),
            )
            .nest(2)
            .group(),
        )
        .append(RcDoc::space())
        .append(RcDoc::text("}"))
}

fn meths_to_doc(meths: &[Binding]) -> RcDoc<()> {
    RcDoc::text("{")
        .append(RcDoc::concat(meths.iter().map(|meth| {
            let doc = RcDoc::line().append(RcDoc::text(format!("{}:", meth.id)));
            let doc = match meth.typ {
                IDLType::VarT(ref var) => doc.append(RcDoc::space().append(RcDoc::text(var))),
                IDLType::FuncT(ref func) => {
                    doc.append(RcDoc::space().append(func.to_doc()).nest(2))
                }
                _ => unreachable!(),
            }
            .nest(2)
            .group();
            doc.append(RcDoc::text(";"))
        })))
        .append(RcDoc::space())
        .append(RcDoc::text("}"))
}

fn args_to_doc(args: &[IDLType]) -> RcDoc<()> {
    RcDoc::text("(")
        .append(
            RcDoc::intersperse(
                args.iter().map(|arg| arg.to_doc()),
                RcDoc::text(",").append(RcDoc::space()),
            )
            .nest(1)
            .group(),
        )
        .append(")")
}
