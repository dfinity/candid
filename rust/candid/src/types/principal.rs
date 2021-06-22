use super::{CandidType, CandidTypeCache, IdlSerialize, Serializer, Type, TypeId};

pub use ic_types::Principal;

impl IdlSerialize for Principal {
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_principal(self.as_slice())
    }
}

impl CandidType for Principal {
    fn id() -> TypeId {
        TypeId::of::<Principal>()
    }
    fn _ty<C: CandidTypeCache>(_c: &mut C) -> Type {
        Type::Principal
    }
}
