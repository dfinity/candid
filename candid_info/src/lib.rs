extern crate candid_derive;
pub use candid_derive::*;

pub mod types;
use types::{Type, TypeId};

mod impls;

pub trait IDLType {
    // memoized type derivation
    fn ty() -> Type {
        let id = Self::id();
        if let Some(t) = types::find_type(id) {
            match t {
                Type::Unknown => Type::Knot(id),
                _ => t,
            }
        } else {
            types::env_add(id, Type::Unknown);
            let t = Self::_ty();
            types::env_add(id, t.clone());
            t
        }
    }
    fn id() -> TypeId;
    fn _ty() -> Type;
    // only used for serialize IDLValue
    fn value_ty(&self) -> Type {
        unreachable!();
    }
    // only serialize the value encoding
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer;
}

pub trait Serializer: Sized {
    type Error;
    type Compound: Compound<Error = Self::Error>;
    fn serialize_bool(self, v: bool) -> Result<(), Self::Error>;
    fn serialize_int(self, v: i64) -> Result<(), Self::Error>;
    fn serialize_nat(self, v: u64) -> Result<(), Self::Error>;
    fn serialize_text(self, v: &str) -> Result<(), Self::Error>;
    fn serialize_null(self, v: ()) -> Result<(), Self::Error>;
    fn serialize_option<T: ?Sized>(self, v: Option<&T>) -> Result<(), Self::Error>
    where
        T: IDLType;
    fn serialize_struct(self) -> Result<Self::Compound, Self::Error>;
    fn serialize_vec(self, len: usize) -> Result<Self::Compound, Self::Error>;
    fn serialize_variant(self, index: u64) -> Result<Self::Compound, Self::Error>;
}

pub trait Compound {
    type Error;
    fn serialize_element<T: ?Sized>(&mut self, v: &T) -> Result<(), Self::Error>
    where
        T: IDLType;
}

// IDL hash function comes from
// https://caml.inria.fr/pub/papers/garrigue-polymorphic_variants-ml98.pdf
pub fn idl_hash(id: &str) -> u32 {
    let mut s: u32 = 0;
    for c in id.chars() {
        s = s.wrapping_mul(223).wrapping_add(c as u32);
    }
    s
}
