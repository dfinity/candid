//! Provides Candid type conversion and serialization.
//!  * `CandidType` trait converts a Rust type to Candid type `types::Type`. The implementation for user-defined data types can be derived from `candid_derive` crate.
//!  * `Serializer` trait serializes a Rust value to Candid binary format.
//!    We do not use Serde's `Serialize` trait because Candid requires serializing types along with the values.
//!    This is difficult to achieve in `Serialize`, especially for enum types.

use serde::ser::Error;

mod impls;
pub mod internal;
pub mod subtype;

pub use self::internal::{get_type, Field, Function, Label, Type, TypeId};

pub mod number;
pub mod principal;
pub mod reference;
pub mod reserved;

pub trait IdlSerialize {
    // only serialize the value encoding
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer;
}

pub trait CandidTyping<Cache = StaticCache>: IdlSerialize {
    fn ty() -> Type
    where
        Cache: Default,
    {
        Self::ty_from_cache(&mut Default::default())
    }

    fn ty_from_cache(c: &mut Cache) -> Type;
}

impl<T: CandidType + ?Sized, Cache: CandidTypeCache> CandidTyping<Cache> for T {
    fn ty_from_cache(c: &mut Cache) -> Type {
        let id = Self::id();
        match c.find_type(&id) {
            Some(Type::Unknown) => Type::Knot(id),
            Some(t) => t,
            None => {
                c.add_type(id.clone(), Type::Unknown);
                let t = Self::_ty(c);
                c.add_type(id, t.clone());
                t
            }
        }
    }
}

pub trait CandidTypeCache {
    fn find_type(&self, id: &TypeId) -> Option<Type>;
    fn add_type(&mut self, id: TypeId, ty: Type);
}

#[derive(Default)]
pub struct StaticCache;

impl CandidTypeCache for StaticCache {
    fn find_type(&self, id: &TypeId) -> Option<Type> {
        self::internal::find_type(&id)
    }
    fn add_type(&mut self, id: TypeId, ty: Type) {
        if ty != Type::Unknown {
            self::internal::env_id(id.clone(), ty.clone());
        }
        self::internal::env_add(id, ty);
    }
}

pub trait CandidType: IdlSerialize {
    // memoized type derivation
    fn id() -> TypeId {
        TypeId::of::<Self>()
    }
    fn _ty<C: CandidTypeCache>(c: &mut C) -> Type;
}

pub trait Serializer: Sized {
    type Error: Error;
    type Compound: Compound<Error = Self::Error>;
    fn serialize_bool(self, v: bool) -> Result<(), Self::Error>;
    fn serialize_int(self, v: &crate::Int) -> Result<(), Self::Error>;
    fn serialize_nat(self, v: &crate::Nat) -> Result<(), Self::Error>;
    fn serialize_nat8(self, v: u8) -> Result<(), Self::Error>;
    fn serialize_nat16(self, v: u16) -> Result<(), Self::Error>;
    fn serialize_nat32(self, v: u32) -> Result<(), Self::Error>;
    fn serialize_nat64(self, v: u64) -> Result<(), Self::Error>;
    fn serialize_int8(self, v: i8) -> Result<(), Self::Error>;
    fn serialize_int16(self, v: i16) -> Result<(), Self::Error>;
    fn serialize_int32(self, v: i32) -> Result<(), Self::Error>;
    fn serialize_int64(self, v: i64) -> Result<(), Self::Error>;
    fn serialize_float32(self, v: f32) -> Result<(), Self::Error>;
    fn serialize_float64(self, v: f64) -> Result<(), Self::Error>;
    fn serialize_text(self, v: &str) -> Result<(), Self::Error>;
    fn serialize_null(self, v: ()) -> Result<(), Self::Error>;
    fn serialize_empty(self) -> Result<(), Self::Error>;
    fn serialize_option<T: ?Sized>(self, v: Option<&T>) -> Result<(), Self::Error>
    where
        T: IdlSerialize;
    fn serialize_struct(self) -> Result<Self::Compound, Self::Error>;
    fn serialize_vec(self, len: usize) -> Result<Self::Compound, Self::Error>;
    fn serialize_blob(self, v: &[u8]) -> Result<(), Self::Error>;
    fn serialize_variant(self, index: u64) -> Result<Self::Compound, Self::Error>;
    fn serialize_principal(self, v: &[u8]) -> Result<(), Self::Error>;
    fn serialize_function(self, v: &[u8], meth: &str) -> Result<(), Self::Error>;
}

pub trait Compound {
    type Error;
    fn serialize_element<T: ?Sized>(&mut self, v: &T) -> Result<(), Self::Error>
    where
        T: IdlSerialize;
    // Used for simulating serde(with = "serde_bytes"). We can remove this when specialization is stable in Rust,
    // or generalize this function to take a closure for with.
    #[doc(hidden)]
    fn serialize_blob(&mut self, blob: &[u8]) -> Result<(), Self::Error>;
}
