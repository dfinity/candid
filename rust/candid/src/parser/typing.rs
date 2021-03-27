use super::types::*;
use crate::types::{Field, Function, Type};
use crate::{Error, Result};
use std::collections::{BTreeMap, BTreeSet};

pub struct Env<'a> {
    pub te: &'a mut TypeEnv,
    pub pre: bool,
}

#[derive(Debug, Clone, Default)]
pub struct TypeEnv(pub BTreeMap<String, Type>);

impl TypeEnv {
    pub fn new() -> Self {
        TypeEnv(BTreeMap::new())
    }
    /// Convert candid AST to internal Type
    pub fn ast_to_type(&self, ast: &super::types::IDLType) -> Result<Type> {
        let env = Env {
            te: &mut self.clone(),
            pre: false,
        };
        check_type(&env, ast)
    }
    pub fn merge<'a>(&'a mut self, env: &TypeEnv) -> Result<&'a mut Self> {
        for (k, v) in env.0.iter() {
            let entry = self.0.entry(k.to_string()).or_insert_with(|| v.clone());
            if *entry != *v {
                return Err(Error::msg("inconsistent binding"));
            }
        }
        Ok(self)
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
    pub fn trace_type<'a>(&'a self, t: &'a Type) -> Result<Type> {
        match t {
            Type::Var(id) => self.trace_type(self.find_type(id)?),
            Type::Knot(ref id) => self.trace_type(&crate::types::internal::find_type(id).unwrap()),
            t => Ok(t.clone()),
        }
    }
    pub fn as_func<'a>(&'a self, t: &'a Type) -> Result<&'a Function> {
        match t {
            Type::Func(f) => Ok(f),
            Type::Var(id) => self.as_func(self.find_type(id)?),
            _ => Err(Error::msg(format!("not a function type: {}", t))),
        }
    }
    pub fn as_service<'a>(&'a self, t: &'a Type) -> Result<&'a [(String, Type)]> {
        match t {
            Type::Service(s) => Ok(s),
            Type::Var(id) => self.as_service(self.find_type(id)?),
            Type::Class(_, ty) => self.as_service(&ty),
            _ => Err(Error::msg(format!("not a service type: {}", t))),
        }
    }
    pub fn get_method<'a>(&'a self, t: &'a Type, id: &'a str) -> Result<&'a Function> {
        for (meth, ty) in self.as_service(t)?.iter() {
            if meth == id {
                return self.as_func(ty);
            }
        }
        Err(Error::msg(format!("cannot find method {}", id)))
    }
}
impl std::fmt::Display for TypeEnv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (k, v) in self.0.iter() {
            writeln!(f, "type {} = {}", k, v)?;
        }
        Ok(())
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
        IDLType::PrincipalT => Ok(Type::Principal),
        IDLType::FuncT(func) => {
            let mut t1 = Vec::new();
            for t in func.args.iter() {
                t1.push(check_type(env, t)?);
            }
            let mut t2 = Vec::new();
            for t in func.rets.iter() {
                t2.push(check_type(env, t)?);
            }
            if func.modes.len() > 1 {
                return Err(Error::msg("cannot have more than one mode"));
            }
            if func.modes.len() == 1
                && func.modes[0] == crate::parser::types::FuncMode::Oneway
                && !t2.is_empty()
            {
                return Err(Error::msg("oneway function has non-unit return type"));
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
        IDLType::ClassT(_, _) => Err(Error::msg("service constructor not supported")),
    }
}

pub fn check_unique<'a, I, T>(sorted: I) -> Result<()>
where
    T: 'a + PartialEq + std::fmt::Display,
    I: Iterator<Item = &'a T>,
{
    let mut prev: Option<&T> = None;
    for lab in sorted {
        if let Some(prev) = prev {
            if lab == prev {
                return Err(Error::msg(format!(
                    "label '{}' hash collision with '{}'",
                    lab, prev,
                )));
            }
        }
        prev = Some(lab);
    }
    Ok(())
}

fn check_fields(env: &Env, fs: &[TypeField]) -> Result<Vec<Field>> {
    // field label duplication is checked in the parser
    let mut res = Vec::new();
    for f in fs.iter() {
        let ty = check_type(env, &f.typ)?;
        let field = Field {
            id: f.label.clone(),
            ty,
        };
        res.push(field);
    }
    Ok(res)
}

fn check_meths(env: &Env, ms: &[Binding]) -> Result<Vec<(String, Type)>> {
    // binding duplication is checked in the parser
    let mut res = Vec::new();
    for meth in ms.iter() {
        let t = check_type(env, &meth.typ)?;
        if !env.pre && env.te.as_func(&t).is_err() {
            return Err(Error::msg(format!(
                "method {} is a non-function type {}",
                meth.id,
                meth.typ.to_doc().pretty(80)
            )));
        }
        res.push((meth.id.to_owned(), t));
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

fn check_cycle(env: &TypeEnv) -> Result<()> {
    fn has_cycle<'a>(seen: &mut BTreeSet<&'a str>, env: &'a TypeEnv, t: &'a Type) -> Result<bool> {
        match t {
            Type::Var(id) => {
                if seen.insert(id) {
                    let ty = env.find_type(id)?;
                    has_cycle(seen, env, ty)
                } else {
                    Ok(true)
                }
            }
            _ => Ok(false),
        }
    }
    for (id, ty) in env.0.iter() {
        let mut seen = BTreeSet::new();
        if has_cycle(&mut seen, env, ty)? {
            return Err(Error::msg(format!("{} has cyclic type definition", id)));
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
    check_cycle(env.te)?;
    env.pre = false;
    check_defs(env, decs)?;
    Ok(())
}

fn check_actor(env: &Env, actor: &Option<IDLType>) -> Result<Option<Type>> {
    match actor {
        None => Ok(None),
        Some(IDLType::ClassT(ts, t)) => {
            let mut args = Vec::new();
            for arg in ts.iter() {
                args.push(check_type(env, arg)?);
            }
            let serv = check_type(env, t)?;
            env.te.as_service(&serv)?;
            Ok(Some(Type::Class(args, Box::new(serv))))
        }
        Some(typ) => {
            let t = check_type(env, &typ)?;
            env.te.as_service(&t)?;
            Ok(Some(t))
        }
    }
}

/// Type check IDLProg, and adds bindings to type environment. Returns
/// a hash map for the serivce method signatures. For now, we omit import.
pub fn check_prog(te: &mut TypeEnv, prog: &IDLProg) -> Result<Option<Type>> {
    let mut env = Env { te, pre: false };
    check_decs(&mut env, &prog.decs)?;
    check_actor(&env, &prog.actor)
}
