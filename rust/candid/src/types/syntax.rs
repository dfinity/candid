use crate::types::{FuncMode, Label};
use anyhow::{bail, Result};

#[derive(Debug, Clone, PartialEq, Eq)]
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FuncType {
    pub modes: Vec<FuncMode>,
    pub args: Vec<IDLArgType>,
    pub rets: Vec<IDLType>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeField {
    pub label: Label,
    pub typ: IDLType,
    pub docs: Vec<String>,
}

#[derive(Debug)]
pub enum Dec {
    TypD(Binding),
    ImportType(String),
    ImportServ(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Binding {
    pub id: String,
    pub typ: IDLType,
    pub docs: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct IDLActorType {
    pub typ: IDLType,
    pub docs: Vec<String>,
}

#[derive(Debug)]
pub struct IDLProg {
    pub decs: Vec<Dec>,
    pub actor: Option<IDLActorType>,
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

#[derive(Debug)]
pub struct IDLInitArgs {
    pub decs: Vec<Dec>,
    pub args: Vec<IDLArgType>,
}

#[derive(Debug)]
pub struct IDLMergedProg {
    typ_decs: Vec<Binding>,
    main_actor: Option<IDLActorType>,
    service_imports: Vec<IDLActorType>,
}

impl IDLMergedProg {
    pub fn new(prog: IDLProg) -> IDLMergedProg {
        IDLMergedProg {
            typ_decs: IDLProg::typ_decs(prog.decs).collect(),
            main_actor: prog.actor,
            service_imports: vec![],
        }
    }

    pub fn merge(&mut self, is_service_import: bool, prog: IDLProg) {
        self.typ_decs.extend(IDLProg::typ_decs(prog.decs));
        if is_service_import {
            self.service_imports.push(prog.actor.expect("TODO"))
        }
    }

    pub fn lookup(&self, id: &str) -> Option<&Binding> {
        self.typ_decs.iter().find(|b| b.id == id)
    }

    pub fn decs(&self) -> Vec<Dec> {
        self.typ_decs.iter().map(|b| Dec::TypD(b.clone())).collect()
    }

    pub fn resolve_actor(&self) -> Result<Option<IDLActorType>> {
        let (init_args, top_level_docs, mut methods) = match &self.main_actor {
            None => {
                if self.service_imports.is_empty() {
                    return Ok(None);
                } else {
                    (None, vec![], vec![])
                }
            }
            Some(t) if self.service_imports.is_empty() => return Ok(Some(t.clone())),
            Some(IDLActorType {
                typ: IDLType::ClassT(args, inner),
                docs,
            }) => (
                Some(args.clone()),
                docs.clone(),
                self.chase_service(*inner.clone())?,
            ),
            Some(ty) => (None, ty.docs.clone(), self.chase_service(ty.typ.clone())?),
        };

        for import in &self.service_imports {
            methods.extend(self.chase_service(import.typ.clone())?)
        }

        // TODO: Check for duplicates in methods
        let typ = if let Some(args) = init_args {
            IDLType::ClassT(args, Box::new(IDLType::ServT(methods)))
        } else {
            IDLType::ServT(methods)
        };
        Ok(Some(IDLActorType {
            typ,
            docs: top_level_docs,
        }))
    }

    // TODO: visited set
    fn chase_service(&self, ty: IDLType) -> Result<Vec<Binding>> {
        match ty {
            IDLType::VarT(v) => {
                let resolved = self.typ_decs.iter().find(|b| b.id == v).expect("TODO");
                self.chase_service(resolved.typ.clone())
            }
            IDLType::ServT(bindings) => Ok(bindings),
            _ => bail!("Tried to import a non-service type"),
        }
    }
}
