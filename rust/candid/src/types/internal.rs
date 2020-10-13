use super::CandidType;
use crate::idl_hash;
use num_enum::TryFromPrimitive;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;

// This is a re-implementation of std::any::TypeId to get rid of 'static constraint.
// The current TypeId doesn't consider lifetime while computing the hash, which is
// totally fine for Candid type, as we don't care about lifetime at all.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct TypeId {
    id: usize,
    name: String,
}
impl TypeId {
    pub fn of<T: ?Sized>() -> Self {
        let name = std::any::type_name::<T>();
        let name = name.rsplit("::").next().unwrap();
        let name: String = name
            .chars()
            .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
            .collect();
        TypeId {
            id: TypeId::of::<T> as usize,
            name,
        }
    }
}
impl std::fmt::Display for TypeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

/// Used for candid_derive::export_service to generate TypeEnv from Type
#[derive(Default)]
pub struct TypeContainer {
    pub env: crate::TypeEnv,
}
impl TypeContainer {
    pub fn new() -> Self {
        TypeContainer {
            env: crate::TypeEnv::new(),
        }
    }
    pub fn add<T: CandidType>(&mut self) -> Type {
        let t = T::ty();
        self.go(&t)
    }
    fn go(&mut self, t: &Type) -> Type {
        match t {
            Type::Opt(ref t) => Type::Opt(Box::new(self.go(t))),
            Type::Vec(ref t) => Type::Vec(Box::new(self.go(t))),
            Type::Record(fs) => {
                let res = Type::Record(
                    fs.iter()
                        .map(|Field { id, ty }| Field {
                            id: id.clone(),
                            ty: self.go(ty),
                        })
                        .collect(),
                );
                if t.is_tuple() {
                    return res;
                }
                let id = NAME.with(|n| n.borrow().get(t).cloned());
                if let Some(id) = id {
                    self.env.0.insert(id.to_string(), res);
                    Type::Var(id.to_string())
                } else {
                    // if the type is part of an enum, the id won't be recorded.
                    // we want to inline the type in this case.
                    res
                }
            }
            Type::Variant(fs) => {
                let res = Type::Variant(
                    fs.iter()
                        .map(|Field { id, ty }| Field {
                            id: id.clone(),
                            ty: self.go(ty),
                        })
                        .collect(),
                );
                let id = NAME.with(|n| n.borrow().get(t).cloned());
                if let Some(id) = id {
                    self.env.0.insert(id.to_string(), res);
                    Type::Var(id.to_string())
                } else {
                    res
                }
            }
            Type::Knot(id) => {
                let name = id.to_string();
                let ty = ENV.with(|e| e.borrow().get(id).unwrap().clone());
                self.env.0.insert(id.to_string(), ty);
                Type::Var(name)
            }
            // TODO Func, service
            _ => t.clone(),
        }
    }
}

#[derive(Debug, PartialEq, Hash, Eq, Clone)]
pub enum Type {
    Null,
    Bool,
    Nat,
    Int,
    Nat8,
    Nat16,
    Nat32,
    Nat64,
    Int8,
    Int16,
    Int32,
    Int64,
    Float32,
    Float64,
    Text,
    Reserved,
    Empty,
    Knot(TypeId), // For recursive types from Rust
    Var(String),  // For variables from Candid file
    Unknown,
    Opt(Box<Type>),
    Vec(Box<Type>),
    Record(Vec<Field>),
    Variant(Vec<Field>),
    Func(Function),
    Service(Vec<(String, Type)>),
    Class(Vec<Type>, Box<Type>),
    Principal,
}
impl Type {
    pub(crate) fn is_tuple(&self) -> bool {
        match self {
            Type::Record(ref fs) => {
                for (i, field) in fs.iter().enumerate() {
                    if field.id.get_id() != (i as u32) {
                        return false;
                    }
                }
                true
            }
            _ => false,
        }
    }
}
impl fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", crate::bindings::candid::pp_ty(&self).pretty(80))
    }
}

#[derive(Debug, Eq, Clone)]
pub enum Label {
    Id(u32),
    Named(String),
    Unnamed(u32),
}

impl Label {
    pub fn get_id(&self) -> u32 {
        match *self {
            Label::Id(n) => n,
            Label::Named(ref n) => idl_hash(n),
            Label::Unnamed(n) => n,
        }
    }
}

impl std::fmt::Display for Label {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Label::Id(n) | Label::Unnamed(n) => {
                write!(f, "{}", super::number::pp_num_str(&n.to_string()))
            }
            Label::Named(id) => write!(f, "{}", id),
        }
    }
}

impl PartialEq for Label {
    fn eq(&self, other: &Self) -> bool {
        self.get_id() == other.get_id()
    }
}

impl std::hash::Hash for Label {
    fn hash<H: std::hash::Hasher>(&self, _state: &mut H) {
        self.get_id();
    }
}

#[derive(Debug, PartialEq, Hash, Eq, Clone)]
pub struct Field {
    pub id: Label,
    pub ty: Type,
}

#[derive(Debug, PartialEq, Hash, Eq, Clone)]
pub struct Function {
    pub modes: Vec<crate::parser::types::FuncMode>,
    pub args: Vec<Type>,
    pub rets: Vec<Type>,
}

impl Function {
    pub fn is_query(&self) -> bool {
        self.modes.contains(&crate::parser::types::FuncMode::Query)
    }
}

#[derive(Debug, PartialEq, TryFromPrimitive)]
#[repr(i64)]
pub(crate) enum Opcode {
    Null = -1,
    Bool = -2,
    Nat = -3,
    Int = -4,
    Nat8 = -5,
    Nat16 = -6,
    Nat32 = -7,
    Nat64 = -8,
    Int8 = -9,
    Int16 = -10,
    Int32 = -11,
    Int64 = -12,
    Float32 = -13,
    Float64 = -14,
    Text = -15,
    Reserved = -16,
    Empty = -17,
    Opt = -18,
    Vec = -19,
    Record = -20,
    Variant = -21,
    Principal = -24,
}

pub fn is_primitive(t: &Type) -> bool {
    use self::Type::*;
    match t {
        Null | Bool | Nat | Int | Text => true,
        Nat8 | Nat16 | Nat32 | Nat64 => true,
        Int8 | Int16 | Int32 | Int64 => true,
        Float32 | Float64 => true,
        Reserved | Empty => true,
        Unknown => panic!("Unknown type"),
        Var(_) => panic!("Variable"), // Var may or may not be a primitive, so don't ask me
        Knot(_) => true,
        Opt(_) | Vec(_) | Record(_) | Variant(_) => false,
        Func(_) | Service(_) | Class(_, _) => false,
        Principal => true,
    }
}

pub fn unroll(t: &Type) -> Type {
    use self::Type::*;
    match t {
        Knot(ref id) => find_type(id).unwrap(),
        Opt(ref t) => Opt(Box::new(unroll(t))),
        Vec(ref t) => Vec(Box::new(unroll(t))),
        Record(fs) => Record(
            fs.iter()
                .map(|Field { id, ty }| Field {
                    id: id.clone(),
                    ty: unroll(ty),
                })
                .collect(),
        ),
        Variant(fs) => Variant(
            fs.iter()
                .map(|Field { id, ty }| Field {
                    id: id.clone(),
                    ty: unroll(ty),
                })
                .collect(),
        ),
        _ => (*t).clone(),
    }
}

thread_local! {
    static ENV: RefCell<HashMap<TypeId, Type>> = RefCell::new(HashMap::new());
    static NAME: RefCell<HashMap<Type, TypeId>> = RefCell::new(HashMap::new());
}

pub(crate) fn find_type(id: &TypeId) -> Option<Type> {
    ENV.with(|e| match e.borrow().get(id) {
        None => None,
        Some(t) => Some((*t).clone()),
    })
}

// only for debugging
#[allow(dead_code)]
pub(crate) fn show_env() {
    ENV.with(|e| println!("{:?}", e.borrow()));
}

pub(crate) fn env_add(id: TypeId, t: Type) {
    ENV.with(|e| drop(e.borrow_mut().insert(id.clone(), t.clone())));
    NAME.with(|n| n.borrow_mut().insert(t, id));
}

pub fn get_type<T>(_v: &T) -> Type
where
    T: CandidType,
{
    T::ty()
}
