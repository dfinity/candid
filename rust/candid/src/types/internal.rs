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
        write!(f, "{name}")
    }
}
pub fn type_of<T>(_: &T) -> TypeId {
    TypeId::of::<T>()
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
                        format!("{name}_{v}")
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
        match t.as_ref() {
            TypeInner::Opt(t) => TypeInner::Opt(self.go(t)),
            TypeInner::Vec(t) => TypeInner::Vec(self.go(t)),
            TypeInner::Record(fs) => {
                let res: Type = TypeInner::Record(
                    fs.iter()
                        .map(|Field { id, ty }| Field {
                            id: id.clone(),
                            ty: self.go(ty),
                        })
                        .collect(),
                )
                .into();
                if t.is_tuple() {
                    return res;
                }
                let id = ID.with(|n| n.borrow().get(t).cloned());
                if let Some(id) = id {
                    self.env.0.insert(id.to_string(), res);
                    TypeInner::Var(id.to_string())
                } else {
                    // if the type is part of an enum, the id won't be recorded.
                    // we want to inline the type in this case.
                    return res;
                }
            }
            TypeInner::Variant(fs) => {
                let res: Type = TypeInner::Variant(
                    fs.iter()
                        .map(|Field { id, ty }| Field {
                            id: id.clone(),
                            ty: self.go(ty),
                        })
                        .collect(),
                )
                .into();
                let id = ID.with(|n| n.borrow().get(t).cloned());
                if let Some(id) = id {
                    self.env.0.insert(id.to_string(), res);
                    TypeInner::Var(id.to_string())
                } else {
                    return res;
                }
            }
            TypeInner::Knot(id) => {
                let name = id.to_string();
                let ty = ENV.with(|e| e.borrow().get(id).unwrap().clone());
                self.env.0.insert(id.to_string(), ty);
                TypeInner::Var(name)
            }
            TypeInner::Func(func) => TypeInner::Func(Function {
                modes: func.modes.clone(),
                args: func.args.iter().map(|arg| self.go(arg)).collect(),
                rets: func.rets.iter().map(|arg| self.go(arg)).collect(),
            }),
            TypeInner::Service(serv) => TypeInner::Service(
                serv.iter()
                    .map(|(id, t)| (id.clone(), self.go(t)))
                    .collect(),
            ),
            TypeInner::Class(inits, ref ty) => {
                TypeInner::Class(inits.iter().map(|t| self.go(t)).collect(), self.go(ty))
            }
            t => t.clone(),
        }
        .into()
    }
}
#[cfg(feature = "arc_type")]
#[derive(Debug, PartialEq, Hash, Eq, Clone)]
#[deprecated(
    note = "Do not use arc_type feature! There is a 20% to 80% slowdown in deserialization."
)]
pub struct Type(pub std::sync::Arc<TypeInner>);

#[cfg(not(feature = "arc_type"))]
#[derive(Debug, PartialEq, Hash, Eq, Clone)]
pub struct Type(pub std::rc::Rc<TypeInner>);

#[derive(Debug, PartialEq, Hash, Eq, Clone)]
pub enum TypeInner {
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
    Opt(Type),
    Vec(Type),
    Record(Vec<Field>),
    Variant(Vec<Field>),
    Func(Function),
    Service(Vec<(String, Type)>),
    Class(Vec<Type>, Type),
    Principal,
    Future,
}
impl std::ops::Deref for Type {
    type Target = TypeInner;
    #[inline(always)]
    fn deref(&self) -> &TypeInner {
        self.0.deref()
    }
}
impl AsRef<TypeInner> for Type {
    #[inline(always)]
    fn as_ref(&self) -> &TypeInner {
        self.0.as_ref()
    }
}
impl From<TypeInner> for Type {
    fn from(t: TypeInner) -> Self {
        Type(t.into())
    }
}
impl TypeInner {
    pub fn is_tuple(&self) -> bool {
        match self {
            TypeInner::Record(ref fs) => {
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
impl Type {
    pub fn is_tuple(&self) -> bool {
        self.as_ref().is_tuple()
    }
    pub fn subst(&self, tau: &std::collections::BTreeMap<String, String>) -> Self {
        use TypeInner::*;
        match self.as_ref() {
            Var(id) => match tau.get(id) {
                None => Var(id.to_string()),
                Some(new_id) => Var(new_id.to_string()),
            },
            Opt(t) => Opt(t.subst(tau)),
            Vec(t) => Vec(t.subst(tau)),
            Record(fs) => Record(
                fs.iter()
                    .map(|Field { id, ty }| Field {
                        id: id.clone(),
                        ty: ty.subst(tau),
                    })
                    .collect(),
            ),
            Variant(fs) => Variant(
                fs.iter()
                    .map(|Field { id, ty }| Field {
                        id: id.clone(),
                        ty: ty.subst(tau),
                    })
                    .collect(),
            ),
            Func(func) => {
                let func = func.clone();
                Func(Function {
                    modes: func.modes,
                    args: func.args.into_iter().map(|t| t.subst(tau)).collect(),
                    rets: func.rets.into_iter().map(|t| t.subst(tau)).collect(),
                })
            }
            Service(serv) => Service(
                serv.iter()
                    .map(|(meth, ty)| (meth.clone(), ty.subst(tau)))
                    .collect(),
            ),
            Class(args, ty) => Class(args.iter().map(|t| t.subst(tau)).collect(), ty.subst(tau)),
            _ => return self.clone(),
        }
        .into()
    }
}
impl fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", crate::bindings::candid::pp_ty(self).pretty(80))
    }
}
impl fmt::Display for TypeInner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            crate::bindings::candid::pp_ty_inner(self).pretty(80)
        )
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
            Label::Named(id) => write!(f, "{id}"),
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

#[cfg(feature = "arc_type")]
#[deprecated(
    note = "Do not use arc_type feature! There is a 20% to 80% slowdown in deserialization."
)]
pub type SharedLabel = std::sync::Arc<Label>;

#[cfg(not(feature = "arc_type"))]
pub type SharedLabel = std::rc::Rc<Label>;

#[derive(Debug, PartialEq, Hash, Eq, Clone)]
pub struct Field {
    pub id: SharedLabel,
    pub ty: Type,
}
#[macro_export]
/// Construct a field type, which can be used in `TypeInner::Record` and `TypeInner::Variant`.
///
/// `field!{ a: TypeInner::Nat.into() }` expands to `Field { id: Label::Named("a"), ty: ... }`
/// `field!{ 0: TypeInner::Nat.into() }` expands to `Field { id: Label::Id(0), ty: ... }`
macro_rules! field {
    { $id:tt : $ty:expr } => {
        $crate::types::internal::Field {
            id: match stringify!($id).parse::<u32>() {
                Ok(id) => $crate::types::Label::Id(id),
                Err(_) => $crate::types::Label::Named(stringify!($id).to_string()),
            }.into(),
            ty: $ty
        }
    };
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FuncMode {
    Oneway,
    Query,
    CompositeQuery,
}
impl FuncMode {
    pub(crate) fn to_doc(&self) -> pretty::RcDoc {
        match self {
            FuncMode::Oneway => pretty::RcDoc::text("oneway"),
            FuncMode::Query => pretty::RcDoc::text("query"),
            FuncMode::CompositeQuery => pretty::RcDoc::text("composite_query"),
        }
    }
    pub fn str_to_enum(str: &str) -> Option<Self> {
        match str {
            "oneway" => Some(FuncMode::Oneway),
            "query" => Some(FuncMode::Query),
            "composite_query" => Some(FuncMode::CompositeQuery),
            _ => None,
        }
    }
}
#[derive(Debug, PartialEq, Hash, Eq, Clone)]
pub struct Function {
    pub modes: Vec<FuncMode>,
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
    /// Check a function is a query or composite_query method
    pub fn is_query(&self) -> bool {
        self.modes
            .iter()
            .any(|m| matches!(m, FuncMode::Query | FuncMode::CompositeQuery))
    }
}
#[macro_export]
/// Construct a function type.
///
/// `func!((u8, &str) -> (Nat) query)` expands to `Type(Rc::new(TypeInner::Func(...)))`
macro_rules! func {
    ( ( $($arg:ty),* ) -> ( $($ret:ty),* ) ) => {
        Into::<$crate::types::Type>::into($crate::types::TypeInner::Func($crate::types::Function { args: vec![$(<$arg>::ty()),*], rets: vec![$(<$ret>::ty()),*], modes: vec![] }))
    };
    ( ( $($arg:ty),* ) -> ( $($ret:ty),* ) query ) => {
        Into::<$crate::types::Type>::into($crate::types::TypeInner::Func($crate::types::Function { args: vec![$(<$arg>::ty()),*], rets: vec![$(<$ret>::ty()),*], modes: vec![$crate::types::FuncMode::Query] }))
    };
    ( ( $($arg:ty),* ) -> ( $($ret:ty),* ) composite_query ) => {
        Into::<$crate::types::Type>::into($crate::types::TypeInner::Func($crate::types::Function { args: vec![$(<$arg>::ty()),*], rets: vec![$(<$ret>::ty()),*], modes: vec![$crate::types::FuncMode::CompositeQuery] }))
    };
    ( ( $($arg:ty),* ) -> ( $($ret:ty),* ) oneway ) => {
        Into::<$crate::types::Type>::into($crate::types::TypeInner::Func($crate::types::Function { args: vec![$(<$arg>::ty()),*], rets: vec![$(<$ret>::ty()),*], modes: vec![$crate::types::FuncMode::Oneway] }))
    };
}
#[macro_export]
/// Construct a service type.
///
/// `service!{ "f": func!((HttpRequest) -> ()) }` expands to `Type(Rc::new(TypeInner::Service(...)))`
macro_rules! service {
    { $($meth:tt : $ty:expr);* } => {
        Into::<$crate::types::Type>::into($crate::types::TypeInner::Service(vec![ $(($meth.to_string(), $ty)),* ]))
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
    use self::TypeInner::*;
    match t.as_ref() {
        Null | Bool | Nat | Int | Text => true,
        Nat8 | Nat16 | Nat32 | Nat64 => true,
        Int8 | Int16 | Int32 | Int64 => true,
        Float32 | Float64 => true,
        Reserved | Empty => true,
        Unknown => panic!("Unknown type"),
        Future => panic!("Future type"),
        Var(_) => panic!("Variable"), // Var may or may not be a primitive, so don't ask me
        Knot(_) => true,
        Opt(_) | Vec(_) | Record(_) | Variant(_) => false,
        Func(_) | Service(_) | Class(_, _) => false,
        Principal => true,
    }
}

pub fn unroll(t: &Type) -> Type {
    use self::TypeInner::*;
    match t.as_ref() {
        Knot(ref id) => return find_type(id).unwrap(),
        Opt(ref t) => Opt(unroll(t)),
        Vec(ref t) => Vec(unroll(t)),
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
        t => t.clone(),
    }
    .into()
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
