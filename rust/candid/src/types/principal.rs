use super::{CandidType, Serializer, Type, TypeId};

pub type Principal = ic_types::principal::Principal;

impl CandidType for ic_types::principal::Principal {
    fn id() -> TypeId {
        TypeId::of::<ic_types::principal::Principal>()
    }
    fn _ty() -> Type {
        Type::Principal
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_principal(self.as_slice())
    }
}
