mod impls;
pub mod internal;

pub use self::internal::{get_type, Field, Type, TypeId};

pub trait CandidType {
    // memoized type derivation
    fn ty() -> Type {
        let id = Self::id();
        if let Some(t) = self::internal::find_type(id) {
            match t {
                Type::Unknown => Type::Knot(id),
                _ => t,
            }
        } else {
            self::internal::env_add(id, Type::Unknown);
            let t = Self::_ty();
            self::internal::env_add(id, t.clone());
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
        T: CandidType;
    fn serialize_struct(self) -> Result<Self::Compound, Self::Error>;
    fn serialize_vec(self, len: usize) -> Result<Self::Compound, Self::Error>;
    fn serialize_variant(self, index: u64) -> Result<Self::Compound, Self::Error>;
}

pub trait Compound {
    type Error;
    fn serialize_element<T: ?Sized>(&mut self, v: &T) -> Result<(), Self::Error>
    where
        T: CandidType;
}
