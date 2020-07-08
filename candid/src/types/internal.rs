use super::CandidType;
use crate::idl_hash;
use num_enum::TryFromPrimitive;
use std::cell::RefCell;
use std::collections::HashMap;

// This is a re-implementation of std::any::TypeId to get rid of 'static constraint.
// The current TypeId doesn't consider lifetime while computing the hash, which is
// totally fine for IDL type, as we don't care about lifetime at all.
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct TypeId {
    id: usize,
}
impl TypeId {
    pub fn of<T: ?Sized>() -> Self {
        TypeId {
            id: TypeId::of::<T> as usize,
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
    Principal,
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
            Label::Id(n) | Label::Unnamed(n) => write!(f, "{}", n),
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
    pub hash: u32, // hash is necessary to support field rename attributes
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
        Func(_) | Service(_) => false,
        Principal => true,
    }
}

pub fn unroll(t: &Type) -> Type {
    use self::Type::*;
    match t {
        Knot(id) => find_type(*id).unwrap(),
        Opt(ref t) => Opt(Box::new(unroll(t))),
        Vec(ref t) => Vec(Box::new(unroll(t))),
        Record(fs) => Record(
            fs.iter()
                .map(|Field { id, hash, ty }| Field {
                    id: id.clone(),
                    hash: *hash,
                    ty: unroll(ty),
                })
                .collect(),
        ),
        Variant(fs) => Variant(
            fs.iter()
                .map(|Field { id, hash, ty }| Field {
                    id: id.clone(),
                    hash: *hash,
                    ty: unroll(ty),
                })
                .collect(),
        ),
        _ => (*t).clone(),
    }
}

thread_local! {
    static ENV: RefCell<HashMap<TypeId, Type>> = RefCell::new(HashMap::new());
}

pub(crate) fn find_type(id: TypeId) -> Option<Type> {
    ENV.with(|e| match e.borrow().get(&id) {
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
    ENV.with(|e| drop(e.borrow_mut().insert(id, t)))
}

pub fn get_type<T>(_v: &T) -> Type
where
    T: CandidType,
{
    T::ty()
}
