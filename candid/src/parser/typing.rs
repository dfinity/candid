use super::types::*;
use crate::types::{Field, Function, Type};
use crate::{Error, Result};
use std::collections::HashMap;

pub struct Env<'a> {
    pub te: &'a mut TypeEnv,
    pub pre: bool,
}
#[derive(Debug, Clone, Default)]
pub struct TypeEnv(pub HashMap<String, Type>);
pub type ActorEnv = HashMap<String, Function>;

impl TypeEnv {
    pub fn new() -> Self {
        TypeEnv(HashMap::new())
    }
    /// Generate TypeEnv from type definitions in .did file
    pub fn from_candid(prog: &IDLProg) -> Result<Self> {
        let mut env = TypeEnv::new();
        check_prog(&mut env, prog)?;
        Ok(env)
    }
    /// Convert candid AST to internal Type
    pub fn ast_to_type(&self, ast: &super::types::IDLType) -> Result<Type> {
        let env = Env {
            te: &mut self.clone(),
            pre: false,
        };
        check_type(&env, ast)
    }
    pub fn find_type(&self, name: &str) -> Result<&Type> {
        match self.0.get(name) {
            None => Err(Error::msg(format!("Unbound type identifier {}", name))),
            Some(t) => Ok(t),
        }
    }
    pub fn rec_find_type(&self, name: &str) -> Result<&Type> {
        match self.find_type(name)? {
            Type::Var(id) => self.rec_find_type(id),
            t => Ok(t),
        }
    }
    pub fn as_func<'a>(&'a self, t: &'a Type) -> Result<&'a Function> {
        match t {
            Type::Func(f) => Ok(f),
            Type::Var(id) => self.as_func(self.find_type(id)?),
            _ => Err(Error::msg(format!("not a function type: {:?}", t))),
        }
    }
    pub fn as_service<'a>(&'a self, t: &'a Type) -> Result<&'a [(String, Function)]> {
        match t {
            Type::Service(s) => Ok(s),
            Type::Var(id) => self.as_service(self.find_type(id)?),
            _ => Err(Error::msg(format!("not a service type: {:?}", t))),
        }
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

pub fn check_type(env: &Env, t: &IDLType) -> Result<Type> {
    match t {
        IDLType::PrimT(prim) => Ok(check_prim(prim)),
        IDLType::VarT(id) => {
            env.te.find_type(id)?;
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
        IDLType::FuncT(func) => {
            // TODO check for modes
            let mut t1 = Vec::new();
            for t in func.args.iter() {
                t1.push(check_type(env, t)?);
            }
            let mut t2 = Vec::new();
            for t in func.rets.iter() {
                t2.push(check_type(env, t)?);
            }
            let f = Function {
                modes: func.modes.clone(),
                args: t1,
                rets: t2,
            };
            Ok(Type::Func(f))
        }
        IDLType::ServT(ms) => {
            let ms = check_meths(env, ms)?;
            Ok(Type::Service(ms))
        }
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

fn check_meths(env: &Env, ms: &[Binding]) -> Result<Vec<(String, Function)>> {
    let mut res = Vec::new();
    // TODO check duplicates, sorting
    for meth in ms.iter() {
        let t = check_type(env, &meth.typ)?;
        if !env.pre {
            let func = env.te.as_func(&t)?;
            res.push((meth.id.to_owned(), func.clone()));
        }
    }
    Ok(res)
}

fn check_defs(env: &mut Env, decs: &[Dec]) -> Result<()> {
    for dec in decs.iter() {
        match dec {
            Dec::TypD(Binding { id, typ }) => {
                let t = check_type(env, typ)?;
                env.te.0.insert(id.to_string(), t);
            }
            Dec::ImportD(_) => (),
        }
    }
    Ok(())
}

fn check_decs(env: &mut Env, decs: &[Dec]) -> Result<()> {
    for dec in decs.iter() {
        if let Dec::TypD(Binding { id, typ: _ }) = dec {
            let duplicate = env.te.0.insert(id.to_string(), Type::Unknown);
            if duplicate.is_some() {
                return Err(Error::msg(format!("duplicate binding for {}", id)));
            }
        }
    }
    env.pre = true;
    check_defs(env, decs)?;
    // TODO check for cycle
    env.pre = false;
    check_defs(env, decs)?;
    Ok(())
}

fn check_actor(env: &Env, actor: &Option<IDLType>) -> Result<ActorEnv> {
    match actor {
        None => Ok(HashMap::new()),
        Some(typ) => {
            let t = check_type(env, &typ)?;
            let service = env.te.as_service(&t)?;
            let env = service.iter().cloned().collect();
            Ok(env)
        }
    }
}

pub fn check_prog(te: &mut TypeEnv, prog: &IDLProg) -> Result<ActorEnv> {
    let mut env = Env { te, pre: false };
    check_decs(&mut env, &prog.decs)?;
    let actor = check_actor(&env, &prog.actor)?;
    Ok(actor)
}
