use crate::types::syntax::{Binding, IDLArgType, IDLType, PrimType, TypeField};
use crate::types::{ArgType, Field, FuncMode, Function, Type, TypeInner};
use crate::{Error, Result};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, Default)]
pub struct TypeEnv(pub BTreeMap<String, Type>);

impl TypeEnv {
    pub fn new() -> Self {
        TypeEnv(BTreeMap::new())
    }
    pub fn merge<'a>(&'a mut self, env: &TypeEnv) -> Result<&'a mut Self> {
        for (k, v) in &env.0 {
            let entry = self.0.entry(k.to_string()).or_insert_with(|| v.clone());
            if *entry != *v {
                return Err(Error::msg("inconsistent binding"));
            }
        }
        Ok(self)
    }
    pub fn merge_type(&mut self, env: TypeEnv, ty: Type) -> Type {
        let tau: BTreeMap<String, String> = env
            .0
            .keys()
            .filter(|k| self.0.contains_key(*k))
            .map(|k| (k.clone(), format!("{k}/1")))
            .collect();
        for (k, t) in env.0 {
            let t = t.subst(&tau);
            if let Some(new_key) = tau.get(&k) {
                self.0.insert(new_key.clone(), t);
            } else {
                self.0.insert(k, t);
            }
        }
        ty.subst(&tau)
    }
    pub fn find_type(&self, name: &str) -> Result<&Type> {
        match self.0.get(name) {
            None => Err(Error::msg(format!("Unbound type identifier {name}"))),
            Some(t) => Ok(t),
        }
    }
    pub fn rec_find_type(&self, name: &str) -> Result<&Type> {
        let t = self.find_type(name)?;
        match t.as_ref() {
            TypeInner::Var(id) => self.rec_find_type(id),
            _ => Ok(t),
        }
    }
    pub fn trace_type<'a>(&'a self, t: &'a Type) -> Result<Type> {
        match t.as_ref() {
            TypeInner::Var(id) => self.trace_type(self.find_type(id)?),
            TypeInner::Knot(ref id) => {
                self.trace_type(&crate::types::internal::find_type(id).unwrap())
            }
            _ => Ok(t.clone()),
        }
    }
    pub fn as_func<'a>(&'a self, t: &'a Type) -> Result<&'a Function> {
        match t.as_ref() {
            TypeInner::Func(f) => Ok(f),
            TypeInner::Var(id) => self.as_func(self.find_type(id)?),
            _ => Err(Error::msg(format!("not a function type: {t}"))),
        }
    }
    pub fn as_service<'a>(&'a self, t: &'a Type) -> Result<&'a [(String, Type)]> {
        match t.as_ref() {
            TypeInner::Service(s) => Ok(s),
            TypeInner::Var(id) => self.as_service(self.find_type(id)?),
            TypeInner::Class(_, ty) => self.as_service(ty),
            _ => Err(Error::msg(format!("not a service type: {t}"))),
        }
    }
    pub fn get_method<'a>(&'a self, t: &'a Type, id: &'a str) -> Result<&'a Function> {
        for (meth, ty) in self.as_service(t)? {
            if meth == id {
                return self.as_func(ty);
            }
        }
        Err(Error::msg(format!("cannot find method {id}")))
    }
    fn is_empty<'a>(
        &'a self,
        res: &mut BTreeMap<&'a str, Option<bool>>,
        id: &'a str,
    ) -> Result<bool> {
        match res.get(id) {
            None => {
                res.insert(id, None);
                let t = self.find_type(id)?;
                let result = match t.as_ref() {
                    TypeInner::Record(fs) => {
                        for f in fs {
                            // Assume env only comes from type table, f.ty is either primitive or var.
                            if let TypeInner::Var(f_id) = f.ty.as_ref() {
                                if self.is_empty(res, f_id)? {
                                    res.insert(id, Some(true));
                                    return Ok(true);
                                }
                            }
                        }
                        false
                    }
                    TypeInner::Var(id) => self.is_empty(res, id)?,
                    _ => false,
                };
                res.insert(id, Some(result));
                Ok(result)
            }
            Some(None) => {
                res.insert(id, Some(true));
                Ok(true)
            }
            Some(Some(b)) => Ok(*b),
        }
    }
    pub fn replace_empty(&mut self) -> Result<()> {
        let mut res = BTreeMap::new();
        for name in self.0.keys() {
            self.is_empty(&mut res, name)?;
        }
        let ids: Vec<_> = res
            .iter()
            .filter(|(_, v)| matches!(v, Some(true)))
            .map(|(id, _)| id.to_string())
            .collect();
        for id in ids {
            self.0.insert(id, TypeInner::Empty.into());
        }
        Ok(())
    }

    fn has_cycle<'a>(&'a self, seen: &mut BTreeSet<&'a str>, t: &'a Type) -> Result<bool> {
        match t.as_ref() {
            TypeInner::Var(id) => {
                if seen.insert(id) {
                    let ty = self.find_type(id)?;
                    self.has_cycle(seen, ty)
                } else {
                    Ok(true)
                }
            }
            _ => Ok(false),
        }
    }

    pub fn check_cycle(&self) -> Result<()> {
        for (id, ty) in self.0.iter() {
            let mut seen = BTreeSet::new();
            if self.has_cycle(&mut seen, ty)? {
                return Err(Error::msg(format!("{id} has cyclic type definition")));
            }
        }
        Ok(())
    }

    fn map_arg(&self, arg: &IDLArgType) -> Result<ArgType> {
        Ok(ArgType {
            name: arg.name.clone(),
            typ: self.map_type(&arg.typ)?,
        })
    }

    fn map_fields(&self, fs: &[TypeField]) -> Result<Vec<Field>> {
        // field label duplication is checked in the parser
        let mut res = Vec::new();
        for f in fs.iter() {
            let ty = self.map_type(&f.typ)?;
            let field = Field {
                id: f.label.clone().into(),
                ty,
            };
            res.push(field);
        }
        Ok(res)
    }

    fn map_meths(&self, ms: &[Binding]) -> Result<Vec<(String, Type)>> {
        // binding duplication is checked in the parser
        let mut res = Vec::new();
        for meth in ms.iter() {
            let t = self.map_type(&meth.typ)?;
            if self.as_func(&t).is_err() {
                return Err(Error::msg(format!(
                    "method {} is a non-function type",
                    meth.id
                )));
            }
            res.push((meth.id.to_owned(), t));
        }
        Ok(res)
    }

    pub fn map_type(&self, t: &IDLType) -> Result<Type> {
        match t {
            IDLType::PrimT(prim) => Ok(map_prim(prim)),
            IDLType::VarT(id) => {
                self.find_type(id)?;
                Ok(TypeInner::Var(id.to_string()).into())
            }
            IDLType::OptT(t) => {
                let t = self.map_type(t)?;
                Ok(TypeInner::Opt(t).into())
            }
            IDLType::VecT(t) => {
                let t = self.map_type(t)?;
                Ok(TypeInner::Vec(t).into())
            }
            IDLType::RecordT(fs) => {
                let fs = self.map_fields(fs)?;
                Ok(TypeInner::Record(fs).into())
            }
            IDLType::VariantT(fs) => {
                let fs = self.map_fields(fs)?;
                Ok(TypeInner::Variant(fs).into())
            }
            IDLType::PrincipalT => Ok(TypeInner::Principal.into()),
            IDLType::FuncT(func) => {
                let mut t1 = Vec::new();
                for arg in func.args.iter() {
                    t1.push(self.map_arg(arg)?);
                }
                let mut t2 = Vec::new();
                for t in func.rets.iter() {
                    t2.push(self.map_type(t)?);
                }
                if func.modes.len() > 1 {
                    return Err(Error::msg("cannot have more than one mode"));
                }
                if func.modes.len() == 1 && func.modes[0] == FuncMode::Oneway && !t2.is_empty() {
                    return Err(Error::msg("oneway function has non-unit return type"));
                }
                let f = Function {
                    modes: func.modes.clone(),
                    args: t1,
                    rets: t2,
                };
                Ok(TypeInner::Func(f).into())
            }
            IDLType::ServT(ms) => {
                let ms = self.map_meths(ms)?;
                Ok(TypeInner::Service(ms).into())
            }
            IDLType::ClassT(_, _) => Err(Error::msg("service constructor not supported")),
            IDLType::UnknownT => Err(Error::msg("unknown type")),
        }
    }
}

impl std::fmt::Display for TypeEnv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (k, v) in &self.0 {
            writeln!(f, "type {k} = {v}")?;
        }
        Ok(())
    }
}

fn map_prim(prim: &PrimType) -> Type {
    match prim {
        PrimType::Nat => TypeInner::Nat,
        PrimType::Nat8 => TypeInner::Nat8,
        PrimType::Nat16 => TypeInner::Nat16,
        PrimType::Nat32 => TypeInner::Nat32,
        PrimType::Nat64 => TypeInner::Nat64,
        PrimType::Int => TypeInner::Int,
        PrimType::Int8 => TypeInner::Int8,
        PrimType::Int16 => TypeInner::Int16,
        PrimType::Int32 => TypeInner::Int32,
        PrimType::Int64 => TypeInner::Int64,
        PrimType::Float32 => TypeInner::Float32,
        PrimType::Float64 => TypeInner::Float64,
        PrimType::Bool => TypeInner::Bool,
        PrimType::Text => TypeInner::Text,
        PrimType::Null => TypeInner::Null,
        PrimType::Reserved => TypeInner::Reserved,
        PrimType::Empty => TypeInner::Empty,
    }
    .into()
}
