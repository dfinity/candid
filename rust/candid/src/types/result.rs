use crate::types::{CandidType, Compound, Field, Label, Serializer, Type, TypeInner};
use serde::{Deserialize, Serialize};

#[allow(non_camel_case_types)]
#[derive(Deserialize, Debug, Clone, Serialize)]
pub enum MotokoResult<T, E> {
    ok(T),
    err(E),
}
impl<T, E> MotokoResult<T, E> {
    pub fn into_result(self) -> Result<T, E> {
        match self {
            MotokoResult::ok(v) => Ok(v),
            MotokoResult::err(e) => Err(e),
        }
    }
}
impl<T, E> From<Result<T, E>> for MotokoResult<T, E> {
    fn from(r: Result<T, E>) -> Self {
        match r {
            Ok(v) => MotokoResult::ok(v),
            Err(e) => MotokoResult::err(e),
        }
    }
}
impl<T, E> CandidType for MotokoResult<T, E>
where
    T: CandidType,
    E: CandidType,
{
    fn _ty() -> Type {
        TypeInner::Variant(vec![
            // Make sure the field id is sorted by idl_hash
            Field {
                id: Label::Named("ok".to_owned()).into(),
                ty: T::ty(),
            },
            Field {
                id: Label::Named("err".to_owned()).into(),
                ty: E::ty(),
            },
        ])
        .into()
    }
    fn idl_serialize<S>(&self, serializer: S) -> Result<(), S::Error>
    where
        S: Serializer,
    {
        match *self {
            MotokoResult::ok(ref v) => {
                let mut ser = serializer.serialize_variant(0)?;
                Compound::serialize_element(&mut ser, v)
            }
            MotokoResult::err(ref e) => {
                let mut ser = serializer.serialize_variant(1)?;
                Compound::serialize_element(&mut ser, e)
            }
        }
    }
}
