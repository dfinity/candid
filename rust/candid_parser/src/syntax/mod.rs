mod pretty;

pub use pretty::pretty_print;

use crate::{
    error,
    token::{LexicalError, ParserError, Span, Token, TriviaMap},
};
use anyhow::{anyhow, bail, Context, Result};
use candid::{
    idl_hash,
    types::{FuncMode, Label},
};
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Spanned<T> {
    pub value: T,
    pub span: Span,
}

impl<T> Spanned<T> {
    pub fn new(value: T, span: Span) -> Self {
        Spanned { value, span }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IDLTypeWithSpan {
    pub span: Span,
    pub kind: IDLType,
}

impl IDLTypeWithSpan {
    pub fn new(span: Span, kind: IDLType) -> Self {
        IDLTypeWithSpan { span, kind }
    }

    pub fn synthetic(kind: IDLType) -> Self {
        IDLTypeWithSpan { span: 0..0, kind }
    }
}

impl std::str::FromStr for IDLTypeWithSpan {
    type Err = error::Error;
    fn from_str(str: &str) -> error::Result<Self> {
        let trivia = super::token::TriviaMap::default();
        let lexer = super::token::Tokenizer::new_with_trivia(str, trivia.clone());
        Ok(super::grammar::TypParser::new().parse(Some(&trivia), lexer)?)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IDLType {
    PrimT(PrimType),
    VarT(String),
    FuncT(FuncType),
    OptT(Box<IDLTypeWithSpan>),
    VecT(Box<IDLTypeWithSpan>),
    RecordT(Vec<TypeField>),
    VariantT(Vec<TypeField>),
    ServT(Vec<Binding>),
    ClassT(Vec<IDLTypeWithSpan>, Box<IDLTypeWithSpan>),
    PrincipalT,
}

impl IDLType {
    pub fn is_tuple(&self) -> bool {
        match self {
            IDLType::RecordT(ref fs) => {
                for (i, field) in fs.iter().enumerate() {
                    if field.label.get_id() != (i as u32) {
                        return false;
                    }
                }
                true
            }
            _ => false,
        }
    }
}

impl From<IDLTypeWithSpan> for IDLType {
    fn from(value: IDLTypeWithSpan) -> Self {
        value.kind
    }
}

impl AsRef<IDLType> for IDLTypeWithSpan {
    fn as_ref(&self) -> &IDLType {
        &self.kind
    }
}

impl AsRef<IDLType> for Box<IDLTypeWithSpan> {
    fn as_ref(&self) -> &IDLType {
        &self.kind
    }
}

impl AsRef<IDLType> for IDLType {
    fn as_ref(&self) -> &IDLType {
        self
    }
}

impl std::str::FromStr for IDLType {
    type Err = error::Error;
    fn from_str(str: &str) -> error::Result<Self> {
        Ok(IDLTypeWithSpan::from_str(str)?.kind)
    }
}

#[derive(Debug, Clone)]
pub struct IDLTypes {
    pub args: Vec<IDLTypeWithSpan>,
}

impl std::str::FromStr for IDLTypes {
    type Err = error::Error;
    fn from_str(str: &str) -> error::Result<Self> {
        let trivia = super::token::TriviaMap::default();
        let lexer = super::token::Tokenizer::new_with_trivia(str, trivia.clone());
        Ok(super::grammar::TypsParser::new().parse(Some(&trivia), lexer)?)
    }
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FuncType {
    pub modes: Vec<FuncMode>,
    pub args: Vec<IDLTypeWithSpan>,
    pub rets: Vec<IDLTypeWithSpan>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeField {
    pub label: Label,
    pub typ: IDLTypeWithSpan,
    pub docs: Vec<String>,
    pub span: Span,
}

#[derive(Debug)]
pub enum Dec {
    TypD(Binding),
    ImportType { path: String, span: Span },
    ImportServ { path: String, span: Span },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Binding {
    pub id: String,
    pub typ: IDLTypeWithSpan,
    pub docs: Vec<String>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct IDLActorType {
    pub typ: IDLTypeWithSpan,
    pub docs: Vec<String>,
    pub span: Span,
}

#[derive(Debug)]
pub struct IDLProg {
    pub decs: Vec<Dec>,
    pub actor: Option<IDLActorType>,
    pub span: Span,
}

impl IDLProg {
    pub fn typ_decs(decs: Vec<Dec>) -> impl Iterator<Item = Binding> {
        decs.into_iter().filter_map(|d| {
            if let Dec::TypD(bindings) = d {
                Some(bindings)
            } else {
                None
            }
        })
    }

    pub fn parse_from_tokens<I>(
        trivia: Option<&TriviaMap>,
        tokens: I,
    ) -> std::result::Result<Self, ParserError>
    where
        I: IntoIterator<Item = std::result::Result<(usize, Token, usize), LexicalError>>,
    {
        super::grammar::IDLProgParser::new().parse(trivia, tokens)
    }

    pub fn parse_lossy_from_tokens<I>(
        trivia: Option<&TriviaMap>,
        tokens: I,
    ) -> (Option<Self>, Vec<ParserError>)
    where
        I: IntoIterator<Item = std::result::Result<(usize, Token, usize), LexicalError>>,
    {
        match super::grammar::IDLProgLossyParser::new().parse(trivia, tokens) {
            Ok(result) => result,
            Err(err) => (None, vec![err]),
        }
    }
}

impl std::str::FromStr for IDLProg {
    type Err = error::Error;
    fn from_str(str: &str) -> error::Result<Self> {
        let trivia = super::token::TriviaMap::default();
        let lexer = super::token::Tokenizer::new_with_trivia(str, trivia.clone());
        Ok(Self::parse_from_tokens(Some(&trivia), lexer)?)
    }
}

#[derive(Debug)]
pub struct IDLInitArgs {
    pub decs: Vec<Dec>,
    pub args: Vec<IDLTypeWithSpan>,
    pub span: Span,
}

impl std::str::FromStr for IDLInitArgs {
    type Err = error::Error;
    fn from_str(str: &str) -> error::Result<Self> {
        let trivia = super::token::TriviaMap::default();
        let lexer = super::token::Tokenizer::new_with_trivia(str, trivia.clone());
        Ok(super::grammar::IDLInitArgsParser::new().parse(Some(&trivia), lexer)?)
    }
}

#[derive(Debug)]
pub struct IDLMergedProg {
    typ_decs: Vec<Binding>,
    main_actor: Option<IDLActorType>,
    service_imports: Vec<(String, IDLActorType)>,
}

impl IDLMergedProg {
    pub fn new(prog: IDLProg) -> IDLMergedProg {
        IDLMergedProg {
            typ_decs: IDLProg::typ_decs(prog.decs).collect(),
            main_actor: prog.actor,
            service_imports: vec![],
        }
    }

    pub fn merge(&mut self, is_service_import: bool, name: String, prog: IDLProg) -> Result<()> {
        self.typ_decs.extend(IDLProg::typ_decs(prog.decs));
        if is_service_import {
            let actor = prog
                .actor
                .with_context(|| format!("Imported service file \"{name}\" has no main service"))?;
            self.service_imports.push((name, actor));
        }
        Ok(())
    }

    pub fn lookup(&self, id: &str) -> Option<&Binding> {
        self.typ_decs.iter().find(|b| b.id == id)
    }

    pub fn decs(&self) -> Vec<Dec> {
        self.typ_decs.iter().map(|b| Dec::TypD(b.clone())).collect()
    }

    pub fn bindings(&self) -> impl Iterator<Item = &Binding> {
        self.typ_decs.iter()
    }

    pub fn resolve_actor(&self) -> Result<Option<IDLActorType>> {
        let mut init_args: Option<Vec<IDLTypeWithSpan>> = None;
        let mut top_level_docs: Vec<String> = vec![];
        let mut actor_span: Span = 0..0;
        let mut methods = match &self.main_actor {
            None => {
                if self.service_imports.is_empty() {
                    return Ok(None);
                }
                vec![]
            }
            Some(actor) if self.service_imports.is_empty() => return Ok(Some(actor.clone())),
            Some(actor) => {
                top_level_docs = actor.docs.clone();
                actor_span = actor.span.clone();
                match &actor.typ.kind {
                    IDLType::ClassT(args, inner) => {
                        init_args = Some(args.clone());
                        self.chase_service((**inner).clone(), None)?
                    }
                    _ => self.chase_service(actor.typ.clone(), None)?,
                }
            }
        };

        for (name, typ) in &self.service_imports {
            methods.extend(self.chase_service(typ.typ.clone(), Some(name))?);
            if top_level_docs.is_empty() {
                top_level_docs = typ.docs.clone();
            }
        }

        let mut hashes: HashMap<u32, &str> = HashMap::new();
        for method in &methods {
            let name = &method.id;
            if let Some(previous) = hashes.insert(idl_hash(name), name) {
                bail!("Duplicate imported method name: label '{name}' hash collision with '{previous}'")
            }
        }

        let service_type = IDLTypeWithSpan::synthetic(IDLType::ServT(methods));
        let typ = if let Some(args) = init_args {
            IDLTypeWithSpan::synthetic(IDLType::ClassT(args, Box::new(service_type.clone())))
        } else {
            service_type
        };

        Ok(Some(IDLActorType {
            typ,
            docs: top_level_docs,
            span: actor_span,
        }))
    }

    // NOTE: We don't worry about cyclic type definitions, as we rule those out earlier when checking the type decs
    fn chase_service(
        &self,
        ty: IDLTypeWithSpan,
        import_name: Option<&str>,
    ) -> Result<Vec<Binding>> {
        match ty.kind {
            IDLType::VarT(v) => {
                let resolved = self
                    .typ_decs
                    .iter()
                    .find(|b| b.id == v)
                    .with_context(|| format!("Unbound type identifier {v}"))?;
                self.chase_service(resolved.typ.clone(), import_name)
            }
            IDLType::ServT(bindings) => Ok(bindings),
            ty_kind => Err(import_name
                .map(|name| anyhow!("Imported service file \"{name}\" has a service constructor"))
                .unwrap_or(anyhow!("not a service type: {:?}", ty_kind))),
        }
    }
}
