use super::typing::TypeEnv;
use super::value::{IDLArgs, IDLField, IDLValue};
use crate::types::{Field, Type};
use crate::Result;
use arbitrary::Unstructured;

impl IDLArgs {
    pub fn any(u: &mut Unstructured, env: &TypeEnv, types: &[Type]) -> Result<Self> {
        let mut args = Vec::new();
        for t in types.iter() {
            let v = IDLValue::any(u, env, t)?;
            args.push(v);
        }
        Ok(IDLArgs { args })
    }
}

impl IDLValue {
    pub fn any(u: &mut Unstructured, env: &TypeEnv, ty: &Type) -> Result<Self> {
        Ok(match ty {
            Type::Var(id) => {
                let ty = env.rec_find_type(id)?;
                Self::any(u, env, &ty)?
            }
            Type::Knot(ref id) => {
                let ty = crate::types::internal::find_type(id).unwrap();
                Self::any(u, env, &ty)?
            }
            Type::Null => IDLValue::Null,
            Type::Bool => IDLValue::Bool(u.arbitrary()?),
            Type::Nat => IDLValue::Nat(u.arbitrary::<u128>()?.into()),
            Type::Int => IDLValue::Int(u.arbitrary::<i128>()?.into()),
            Type::Nat8 => IDLValue::Nat8(u.arbitrary()?),
            Type::Nat16 => IDLValue::Nat16(u.arbitrary()?),
            Type::Nat32 => IDLValue::Nat32(u.arbitrary()?),
            Type::Nat64 => IDLValue::Nat64(u.arbitrary()?),
            Type::Int8 => IDLValue::Int8(u.arbitrary()?),
            Type::Int16 => IDLValue::Int16(u.arbitrary()?),
            Type::Int32 => IDLValue::Int32(u.arbitrary()?),
            Type::Int64 => IDLValue::Int64(u.arbitrary()?),
            Type::Float32 => IDLValue::Float32(u.arbitrary()?),
            Type::Float64 => IDLValue::Float64(u.arbitrary()?),
            Type::Text => IDLValue::Text(u.arbitrary()?),
            Type::Reserved => IDLValue::Reserved,
            Type::Principal => IDLValue::Principal(crate::Principal::anonymous()),
            Type::Opt(t) => {
                if u.arbitrary::<bool>()? {
                    IDLValue::Opt(Box::new(Self::any(u, env, t)?))
                } else {
                    IDLValue::None
                }
            }
            Type::Vec(t) => {
                // TODO: use arbitrary_len or a config
                let len = u.int_in_range(0..=50)?;
                let mut vec = Vec::with_capacity(len);
                for _ in 0..len {
                    let e = Self::any(u, env, t)?;
                    vec.push(e);
                }
                IDLValue::Vec(vec)
            }
            Type::Record(fs) => {
                let mut res = Vec::new();
                for Field { id, ty } in fs.iter() {
                    let val = Self::any(u, env, ty)?;
                    res.push(IDLField {
                        id: id.clone(),
                        val,
                    });
                }
                IDLValue::Record(res)
            }
            Type::Variant(fs) => {
                let idx = u.int_in_range(0..=(fs.len() - 1))?;
                let Field { id, ty } = &fs[idx];
                let val = Self::any(u, env, ty)?;
                let field = IDLField {
                    id: id.clone(),
                    val,
                };
                IDLValue::Variant(Box::new(field), idx as u64)
            }
            _ => unimplemented!(),
        })
    }
}
