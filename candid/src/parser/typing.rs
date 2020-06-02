use super::types::*;
use crate::types::{Field, Type};
use crate::{Error, Result};
use std::collections::HashMap;

pub struct Env(pub HashMap<String, Type>);

impl Env {
    pub fn find_type(&self, name: &str) -> Result<&Type> {
        match self.0.get(name) {
            None => Err(Error::msg(format!("Unbound type identifier {}", name))),
            Some(t) => Ok(t),
        }
    }
    pub fn find_concrete_type(&self, name: &str) -> Result<&Type> {
        Ok(match self.find_type(name)? {
            Type::Var(id) => self.find_concrete_type(id)?,
            t => t,
        })
    }
}

fn check_prim(prim: &PrimType) -> Type {
    match prim {
        PrimType::Nat => Type::Nat,
        PrimType::Nat8 => Type::Nat8,
        PrimType::Nat16 => Type::Nat16,
        PrimType::Nat32 => Type::Nat32,
        PrimType::Nat64 => Type::Nat64,
        PrimType::Int => Type::Int,
        PrimType::Int8 => Type::Int8,
        PrimType::Int16 => Type::Int16,
        PrimType::Int32 => Type::Int32,
        PrimType::Int64 => Type::Int64,
        PrimType::Float32 => Type::Float32,
        PrimType::Float64 => Type::Float64,
        PrimType::Bool => Type::Bool,
        PrimType::Text => Type::Text,
        PrimType::Null => Type::Null,
        PrimType::Reserved => Type::Reserved,
        PrimType::Empty => Type::Empty,
    }
}

fn check_type(env: &Env, t: &IDLType) -> Result<Type> {
    match t {
        IDLType::PrimT(prim) => Ok(check_prim(prim)),
        IDLType::VarT(id) => {
            env.find_type(id)?;
            Ok(Type::Var(id.to_string()))
        }
        IDLType::OptT(t) => {
            let t = check_type(env, t)?;
            Ok(Type::Opt(Box::new(t)))
        }
        IDLType::VecT(t) => {
            let t = check_type(env, t)?;
            Ok(Type::Vec(Box::new(t)))
        }
        IDLType::RecordT(fs) => {
            let fs = check_fields(env, fs)?;
            Ok(Type::Record(fs))
        }
        IDLType::VariantT(fs) => {
            let fs = check_fields(env, fs)?;
            Ok(Type::Variant(fs))
        }
        IDLType::FuncT(_) | IDLType::ServT(_) => unimplemented!(),
    }
}

fn check_fields(env: &Env, fs: &[TypeField]) -> Result<Vec<Field>> {
    let mut res = Vec::new();
    {
        let mut prev = None;
        for f in fs.iter() {
            let id = f.label.get_id();
            if let Some(prev) = prev {
                if id == prev {
                    return Err(Error::msg("field name hash collision"));
                }
            }
            prev = Some(id);
        }
    }
    for f in fs.iter() {
        let ty = check_type(env, &f.typ)?;
        let field = match f.label {
            Label::Id(n) | Label::Unnamed(n) => Field {
                id: n.to_string(),
                hash: n,
                ty,
            },
            Label::Named(ref str) => Field {
                id: str.to_string(),
                hash: crate::idl_hash(str),
                ty,
            },
        };
        res.push(field);
    }
    Ok(res)
}

fn check_decs(env: &mut Env, decs: &[Dec]) -> Result<()> {
    for dec in decs.iter() {
        match dec {
            Dec::TypD(Binding { id, typ }) => {
                let t = check_type(env, typ)?;
                env.0.insert(id.to_string(), t);
            }
            Dec::ImportD(_) => (),
        }
    }
    Ok(())
}
/*
fn check_actor(env: &Env, actor: Option<IDLType>) -> Result<Option<IDLType>> {
    match actor {
        None => Ok(None),
        Some(VarT(id)) => unimplemented!(),
        Some(ServT(ms)) => {
            let ms = check_meths(env, ms)?;
            // TODO sort
            Ok(Some(ms))
        }
    }
}
*/
pub fn check_prog(prog: &IDLProg) -> Result<(Env, Option<Type>)> {
    let mut env = Env(HashMap::new());
    // TODO check for cycle
    check_decs(&mut env, &prog.decs)?;
    let actor = None; //check_actor(&env, prog.actor)?;
    Ok((env, actor))
}
