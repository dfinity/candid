use std::{collections::BTreeSet, fmt};

use crate::types::{FuncMode, Label};

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

impl IDLType {
    pub fn is_tuple(&self) -> bool {
        match self {
            IDLType::RecordT(fields) => {
                for (i, field) in fields.iter().enumerate() {
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

impl fmt::Display for IDLType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", crate::pretty::candid::pp_ty(self).pretty(80))
    }
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

#[derive(Debug, Default)]
pub struct IDLEnv {
    pub types_bindings: Vec<Binding>,
    types_bindings_ids: BTreeSet<String>,
    pub actor: Option<IDLType>,
}

impl From<&IDLProg> for IDLEnv {
    fn from(prog: &IDLProg) -> Self {
        let mut types_bindings_ids = BTreeSet::new();
        let mut types_bindings = Vec::new();

        for dec in prog.decs.iter() {
            if let Dec::TypD(binding) = dec {
                let is_duplicate = types_bindings_ids.insert(binding.id.clone());
                if !is_duplicate {
                    types_bindings.push(binding.clone());
                }
            }
        }

        let mut env = Self {
            types_bindings,
            types_bindings_ids,
            actor: None,
        };
        env.set_actor(prog.actor.clone());
        env
    }
}

impl From<Vec<&Binding>> for IDLEnv {
    fn from(bindings: Vec<&Binding>) -> Self {
        let mut env = Self::default();
        for binding in bindings {
            env.insert_binding(binding.clone());
        }
        env
    }
}

impl IDLEnv {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert_binding(&mut self, binding: Binding) {
        let is_new = self.types_bindings_ids.insert(binding.id.clone());
        if is_new {
            self.types_bindings.push(binding);
        }
    }

    pub fn bindings_ids(&self) -> Vec<&str> {
        self.types_bindings_ids
            .iter()
            .map(|id| id.as_str())
            .collect()
    }

    pub fn set_actor(&mut self, actor: Option<IDLType>) {
        self.actor = actor;
    }

    pub fn find_binding(&self, id: &str) -> Result<&Binding, String> {
        self.types_bindings
            .iter()
            .find(|b| b.id == id)
            .ok_or(format!("Unbound type identifier: {id}"))
    }

    pub fn find_type(&self, id: &str) -> Result<&IDLType, String> {
        self.find_binding(id).map(|b| &b.typ)
    }

    pub fn rec_find_type(&self, name: &str) -> Result<&IDLType, String> {
        let t = self.find_type(name)?;
        match t {
            IDLType::VarT(id) => self.rec_find_type(id),
            _ => Ok(t),
        }
    }

    pub fn trace_type(&self, t: &IDLType) -> Result<IDLType, String> {
        match t {
            IDLType::VarT(id) => self.trace_type(self.find_type(id)?),
            IDLType::ClassT(_, t) => self.trace_type(t),
            _ => Ok(t.clone()),
        }
    }

    pub fn as_service<'a>(&'a self, t: &'a IDLType) -> Result<&'a Vec<Binding>, String> {
        match t {
            IDLType::ServT(methods) => Ok(methods),
            IDLType::VarT(id) => self.as_service(self.find_type(id)?),
            IDLType::ClassT(_, t) => self.as_service(t),
            _ => Err(format!("not a service type: {t}")),
        }
    }

    pub fn as_func<'a>(&'a self, t: &'a IDLType) -> Result<&'a FuncType, String> {
        match t {
            IDLType::FuncT(f) => Ok(f),
            IDLType::VarT(id) => self.as_func(self.find_type(id)?),
            _ => Err(format!("not a function type: {:?}", t)),
        }
    }

    pub fn get_method<'a>(&'a self, t: &'a IDLType, id: &'a str) -> Result<&'a FuncType, String> {
        for binding in self.as_service(t)? {
            if binding.id == id {
                return self.as_func(&binding.typ);
            }
        }
        Err(format!("cannot find method {id}"))
    }
}
