use super::{CandidType, Serializer, Type, TypeInner};

pub use ic_principal::{Principal, PrincipalError};

impl CandidType for Principal {
    fn _ty() -> Type {
        TypeInner::Principal.into()
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_principal(self.as_slice())
    }
}
