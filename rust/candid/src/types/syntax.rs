use std::{collections::BTreeMap, fmt};

use crate::{
    types::{ArgType, Field, FuncMode, Function, Label, Type, TypeInner},
    TypeEnv,
};

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

impl From<IDLType> for Type {
    fn from(t: IDLType) -> Self {
        match t {
            IDLType::PrimT(PrimType::Null) => TypeInner::Null,
            IDLType::PrimT(PrimType::Bool) => TypeInner::Bool,
            IDLType::PrimT(PrimType::Nat) => TypeInner::Nat,
            IDLType::PrimT(PrimType::Int) => TypeInner::Int,
            IDLType::PrimT(PrimType::Nat8) => TypeInner::Nat8,
            IDLType::PrimT(PrimType::Nat16) => TypeInner::Nat16,
            IDLType::PrimT(PrimType::Nat32) => TypeInner::Nat32,
            IDLType::PrimT(PrimType::Nat64) => TypeInner::Nat64,
            IDLType::PrimT(PrimType::Int8) => TypeInner::Int8,
            IDLType::PrimT(PrimType::Int16) => TypeInner::Int16,
            IDLType::PrimT(PrimType::Int32) => TypeInner::Int32,
            IDLType::PrimT(PrimType::Int64) => TypeInner::Int64,
            IDLType::PrimT(PrimType::Float32) => TypeInner::Float32,
            IDLType::PrimT(PrimType::Float64) => TypeInner::Float64,
            IDLType::PrimT(PrimType::Text) => TypeInner::Text,
            IDLType::PrimT(PrimType::Reserved) => TypeInner::Reserved,
            IDLType::PrimT(PrimType::Empty) => TypeInner::Empty,
            IDLType::VarT(id) => TypeInner::Var(id),
            IDLType::FuncT(func) => TypeInner::Func(func.into()),
            IDLType::OptT(t) => TypeInner::Opt((*t).into()),
            IDLType::VecT(t) => TypeInner::Vec((*t).into()),
            IDLType::RecordT(fields) => {
                TypeInner::Record(fields.into_iter().map(|t| t.into()).collect())
            }
            IDLType::VariantT(fields) => {
                TypeInner::Variant(fields.into_iter().map(|t| t.into()).collect())
            }
            IDLType::ServT(methods) => {
                TypeInner::Service(methods.into_iter().map(|t| (t.id, t.typ.into())).collect())
            }
            IDLType::ClassT(args, t) => {
                TypeInner::Class(args.into_iter().map(|t| t.into()).collect(), (*t).into())
            }
            IDLType::PrincipalT => TypeInner::Principal,
            IDLType::UnknownT => TypeInner::Unknown,
        }
        .into()
    }
}

impl From<Type> for IDLType {
    fn from(t: Type) -> Self {
        match t.as_ref() {
            TypeInner::Null => IDLType::PrimT(PrimType::Null),
            TypeInner::Bool => IDLType::PrimT(PrimType::Bool),
            TypeInner::Nat => IDLType::PrimT(PrimType::Nat),
            TypeInner::Int => IDLType::PrimT(PrimType::Int),
            TypeInner::Nat8 => IDLType::PrimT(PrimType::Nat8),
            TypeInner::Nat16 => IDLType::PrimT(PrimType::Nat16),
            TypeInner::Nat32 => IDLType::PrimT(PrimType::Nat32),
            TypeInner::Nat64 => IDLType::PrimT(PrimType::Nat64),
            TypeInner::Int8 => IDLType::PrimT(PrimType::Int8),
            TypeInner::Int16 => IDLType::PrimT(PrimType::Int16),
            TypeInner::Int32 => IDLType::PrimT(PrimType::Int32),
            TypeInner::Int64 => IDLType::PrimT(PrimType::Int64),
            TypeInner::Float32 => IDLType::PrimT(PrimType::Float32),
            TypeInner::Float64 => IDLType::PrimT(PrimType::Float64),
            TypeInner::Text => IDLType::PrimT(PrimType::Text),
            TypeInner::Reserved => IDLType::PrimT(PrimType::Reserved),
            TypeInner::Empty => IDLType::PrimT(PrimType::Empty),
            TypeInner::Var(id) => IDLType::VarT(id.to_string()),
            TypeInner::Opt(t) => IDLType::OptT(Box::new(t.clone().into())),
            TypeInner::Vec(t) => IDLType::VecT(Box::new(t.clone().into())),
            TypeInner::Record(fields) => {
                IDLType::RecordT(fields.iter().map(|t| t.clone().into()).collect())
            }
            TypeInner::Variant(fields) => {
                IDLType::VariantT(fields.iter().map(|t| t.clone().into()).collect())
            }
            TypeInner::Func(func) => IDLType::FuncT(func.clone().into()),
            TypeInner::Service(methods) => IDLType::ServT(
                methods
                    .iter()
                    .map(|t| Binding {
                        id: t.0.clone(),
                        typ: t.1.clone().into(),
                    })
                    .collect(),
            ),
            TypeInner::Class(args, t) => IDLType::ClassT(
                args.iter().map(|t| t.clone().into()).collect(),
                Box::new(t.clone().into()),
            ),
            TypeInner::Principal => IDLType::PrincipalT,
            TypeInner::Unknown => IDLType::UnknownT,
            TypeInner::Knot(_) => IDLType::UnknownT,
            TypeInner::Future => IDLType::UnknownT,
        }
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

impl From<FuncType> for Function {
    fn from(t: FuncType) -> Self {
        Function {
            modes: t.modes,
            args: t.args.into_iter().map(|t| t.into()).collect(),
            rets: t.rets.into_iter().map(|t| t.into()).collect(),
        }
    }
}

impl From<Function> for FuncType {
    fn from(t: Function) -> Self {
        FuncType {
            modes: t.modes,
            args: t.args.into_iter().map(|t| t.into()).collect(),
            rets: t.rets.into_iter().map(|t| t.into()).collect(),
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IDLArgType {
    pub typ: IDLType,
    pub name: Option<String>,
}

impl From<IDLArgType> for ArgType {
    fn from(t: IDLArgType) -> Self {
        ArgType {
            typ: t.typ.into(),
            name: t.name,
        }
    }
}

impl From<ArgType> for IDLArgType {
    fn from(t: ArgType) -> Self {
        IDLArgType {
            typ: t.typ.into(),
            name: t.name,
        }
    }
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

impl From<TypeField> for Field {
    fn from(t: TypeField) -> Self {
        Field {
            id: t.label.into(),
            ty: t.typ.into(),
        }
    }
}

impl From<Field> for TypeField {
    fn from(t: Field) -> Self {
        TypeField {
            label: (*t.id).clone(),
            typ: t.ty.into(),
        }
    }
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

impl From<TypeEnv> for IDLEnv {
    fn from(env: TypeEnv) -> Self {
        let mut idl_env = Self::default();
        for (id, t) in env.0 {
            idl_env.insert_binding(Binding { id, typ: t.into() });
        }
        idl_env
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
