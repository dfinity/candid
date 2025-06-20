use std::{collections::BTreeMap, fmt};

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
    UnknownT,
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
    types: BTreeMap<String, Option<IDLType>>,
    types_bindings_ids: Vec<String>,
    pub actor: Option<IDLType>,
}

impl From<&IDLProg> for IDLEnv {
    fn from(prog: &IDLProg) -> Self {
        let mut env = Self::new();

        for dec in prog.decs.iter() {
            if let Dec::TypD(binding) = dec {
                env.insert_binding(binding.clone());
            }
        }

        env.set_actor(prog.actor.clone());
        env
    }
}

impl From<Vec<Binding>> for IDLEnv {
    fn from(bindings: Vec<Binding>) -> Self {
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
        let duplicate = self
            .types
            .insert(binding.id.clone(), Some(binding.typ.clone()));
        if duplicate.is_none() {
            self.types_bindings_ids.push(binding.id.clone());
        }
    }

    pub fn insert_unknown(&mut self, id: &str) {
        let duplicate = self.types.insert(id.to_string(), None);
        if duplicate.is_none() {
            self.types_bindings_ids.push(id.to_string());
        }
    }

    pub fn types_ids(&self) -> Vec<&str> {
        self.types_bindings_ids
            .iter()
            .map(|id| id.as_str())
            .collect()
    }

    pub fn set_actor(&mut self, actor: Option<IDLType>) {
        self.actor = actor;
    }

    pub fn find_binding<'a>(&'a self, id: &'a str) -> Result<(&'a str, &'a IDLType), String> {
        self.find_type(id).map(|t| (id, t))
    }

    pub fn find_type(&self, id: &str) -> Result<&IDLType, String> {
        self.types
            .get(id)
            .ok_or(format!("Type identifier not found: {id}"))
            .and_then(|t| {
                t.as_ref()
                    .ok_or(format!("Type identifier is unknown: {id}"))
            })
    }

    pub fn assert_has_type(&self, id: &str) -> Result<(), String> {
        if self.types.contains_key(id) {
            Ok(())
        } else {
            Err(format!("Type identifier not found: {id}"))
        }
    }

    pub fn get_types(&self) -> Vec<&IDLType> {
        self.types_bindings_ids
            .iter()
            .map(|id| self.find_type(id).unwrap())
            .collect()
    }

    pub fn get_bindings(&self) -> Vec<(&str, &IDLType)> {
        self.types_bindings_ids
            .iter()
            .map(|id| self.find_binding(id).unwrap())
            .collect()
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
