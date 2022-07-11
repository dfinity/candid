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
    pub name: &'static str,
}
impl TypeId {
    pub fn of<T: ?Sized>() -> Self {
        let name = std::any::type_name::<T>();
        TypeId {
            id: TypeId::of::<T> as usize,
            name,
        }
    }
}
impl std::fmt::Display for TypeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = NAME.with(|n| n.borrow_mut().get(self));
        write!(f, "{}", name)
    }
}

#[derive(Default)]
struct TypeName {
    type_name: HashMap<TypeId, String>,
    name_index: HashMap<String, usize>,
}
impl TypeName {
    fn get(&mut self, id: &TypeId) -> String {
        match self.type_name.get(id) {
            Some(n) => n.to_string(),
            None => {
                // The format of id.name is unspecified, and doesn't guarantee to be unique.
                // Splitting by "::" is not ideal, as we can get types like std::Box<lib::List>, HashMap<lib::K, V>
                // This is not a problem for correctness, but I may get misleading names.
                let name = id.name.split('<').next().unwrap();
                let name = name.rsplit("::").next().unwrap();
                let name = name
                    .chars()
                    .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
                    .collect::<String>()
                    .trim_end_matches('_')
                    .to_string();
                let res = match self.name_index.get_mut(&name) {
                    None => {
                        self.name_index.insert(name.clone(), 0);
                        name
                    }
                    Some(v) => {
                        *v += 1;
                        format!("{}_{}", name, v)
                    }
                };
                self.type_name.insert(id.clone(), res.clone());
                res
            }
        }
    }
}

/// Used for `candid_derive::export_service` to generate `TypeEnv` from `Type`.
///
/// It performs a global rewriting of `Type` to resolve:
/// * Duplicate type names in different modules/namespaces.
/// * Give different names to instantiated polymorphic types.
/// * Find the type name of a recursive node `Knot(TypeId)` and convert to `Var` node.
///
/// There are some drawbacks of this approach:
/// * The type name is based on `type_name::<T>()`, whose format is unspecified and long. We use some regex to shorten the name.
/// * Several Rust types can map to the same Candid type, and we only get to remember one name (currently we choose the shortest name). As a result, some of the type names in Rust is lost.
/// * Unless we do equivalence checking, recursive types can be unrolled and assigned to multiple names.
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
                let id = ID.with(|n| n.borrow().get(t).cloned());
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
                let id = ID.with(|n| n.borrow().get(t).cloned());
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
            Type::Func(func) => Type::Func(Function {
                modes: func.modes.clone(),
                args: func.args.iter().map(|arg| self.go(arg)).collect(),
                rets: func.rets.iter().map(|arg| self.go(arg)).collect(),
            }),
            Type::Service(serv) => Type::Service(
                serv.iter()
                    .map(|(id, t)| (id.clone(), self.go(t)))
                    .collect(),
            ),
            Type::Class(inits, ref ty) => Type::Class(
                inits.iter().map(|t| self.go(t)).collect(),
                Box::new(self.go(ty)),
            ),
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
    pub fn subst(self, tau: &std::collections::BTreeMap<String, String>) -> Self {
        use Type::*;
        match self {
            Var(id) => match tau.get(&id) {
                None => Var(id),
                Some(new_id) => Var(new_id.to_string()),
            },
            Opt(t) => Opt(Box::new(t.subst(tau))),
            Vec(t) => Vec(Box::new(t.subst(tau))),
            Record(fs) => Record(
                fs.into_iter()
                    .map(|Field { id, ty }| Field {
                        id,
                        ty: ty.subst(tau),
                    })
                    .collect(),
            ),
            Variant(fs) => Variant(
                fs.into_iter()
                    .map(|Field { id, ty }| Field {
                        id,
                        ty: ty.subst(tau),
                    })
                    .collect(),
            ),
            Func(func) => Func(Function {
                modes: func.modes,
                args: func.args.into_iter().map(|t| t.subst(tau)).collect(),
                rets: func.rets.into_iter().map(|t| t.subst(tau)).collect(),
            }),
            Service(serv) => Service(
                serv.into_iter()
                    .map(|(meth, ty)| (meth, ty.subst(tau)))
                    .collect(),
            ),
            Class(args, ty) => Class(
                args.into_iter().map(|t| t.subst(tau)).collect(),
                Box::new(ty.subst(tau)),
            ),
            _ => self,
        }
    }
}
impl fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", crate::bindings::candid::pp_ty(self).pretty(80))
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
impl fmt::Display for Function {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            crate::bindings::candid::pp_function(self).pretty(80)
        )
    }
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
    Func = -22,
    Service = -23,
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
    // only used for TypeContainer
    static ID: RefCell<HashMap<Type, TypeId>> = RefCell::new(HashMap::new());
    static NAME: RefCell<TypeName> = RefCell::new(Default::default());
}

pub(crate) fn find_type(id: &TypeId) -> Option<Type> {
    ENV.with(|e| e.borrow().get(id).cloned())
}

// only for debugging
#[allow(dead_code)]
pub(crate) fn show_env() {
    ENV.with(|e| println!("{:?}", e.borrow()));
}

pub(crate) fn env_add(id: TypeId, t: Type) {
    ENV.with(|e| drop(e.borrow_mut().insert(id, t)));
}
pub(crate) fn env_clear() {
    ENV.with(|e| e.borrow_mut().clear());
}

pub(crate) fn env_id(id: TypeId, t: Type) {
    // prefer shorter type names
    let new_len = id.name.len();
    ID.with(|n| {
        let mut n = n.borrow_mut();
        match n.get_mut(&t) {
            None => {
                n.insert(t, id);
            }
            Some(v) => {
                if new_len < v.name.len() {
                    *v = id;
                }
            }
        }
    });
}

pub fn get_type<T>(_v: &T) -> Type
where
    T: CandidType,
{
    T::ty()
}
