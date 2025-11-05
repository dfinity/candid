mod pretty;

pub use pretty::pretty_print;

use crate::{error, token::Span};
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
pub struct IDLType {
    pub span: Span,
    pub kind: IDLTypeKind,
}

impl IDLType {
    pub fn new(span: Span, kind: IDLTypeKind) -> Self {
        IDLType { span, kind }
    }

    pub fn is_tuple(&self) -> bool {
        match &self.kind {
            IDLTypeKind::RecordT(ref fs) => fs
                .iter()
                .enumerate()
                .all(|(i, field)| field.label.get_id() == (i as u32)),
            _ => false,
        }
    }

    pub fn synthetic(kind: IDLTypeKind) -> Self {
        IDLType { span: 0..0, kind }
    }
}

impl std::str::FromStr for IDLType {
    type Err = error::Error;
    fn from_str(str: &str) -> error::Result<Self> {
        let trivia = super::token::TriviaMap::default();
        let lexer = super::token::Tokenizer::new_with_trivia(str, trivia.clone());
        Ok(super::grammar::TypParser::new().parse(Some(&trivia), lexer)?)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IDLTypeKind {
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
    pub args: Vec<IDLType>,
    pub rets: Vec<IDLType>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeField {
    pub label: Label,
    pub typ: IDLType,
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
    pub typ: IDLType,
    pub docs: Vec<String>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct IDLActorType {
    pub typ: IDLType,
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
}

impl std::str::FromStr for IDLProg {
    type Err = error::Error;
    fn from_str(str: &str) -> error::Result<Self> {
        let trivia = super::token::TriviaMap::default();
        let lexer = super::token::Tokenizer::new_with_trivia(str, trivia.clone());
        Ok(super::grammar::IDLProgParser::new().parse(Some(&trivia), lexer)?)
    }
}

#[derive(Debug)]
pub struct IDLInitArgs {
    pub decs: Vec<Dec>,
    pub args: Vec<IDLType>,
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
        let mut init_args: Option<Vec<IDLType>> = None;
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
                    IDLTypeKind::ClassT(args, inner) => {
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

        let service_type = IDLType::synthetic(IDLTypeKind::ServT(methods));
        let typ = if let Some(args) = init_args {
            IDLType::synthetic(IDLTypeKind::ClassT(args, Box::new(service_type.clone())))
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
    fn chase_service(&self, ty: IDLType, import_name: Option<&str>) -> Result<Vec<Binding>> {
        match ty.kind {
            IDLTypeKind::VarT(v) => {
                let resolved = self
                    .typ_decs
                    .iter()
                    .find(|b| b.id == v)
                    .with_context(|| format!("Unbound type identifier {v}"))?;
                self.chase_service(resolved.typ.clone(), import_name)
            }
            IDLTypeKind::ServT(bindings) => Ok(bindings),
            ty_kind => Err(import_name
                .map(|name| anyhow!("Imported service file \"{name}\" has a service constructor"))
                .unwrap_or(anyhow!("not a service type: {:?}", ty_kind))),
        }
    }
}
