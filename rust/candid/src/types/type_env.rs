use crate::types::{Function, Type, TypeInner};
use crate::utils::RecursionDepth;
use crate::{Error, Result};
use std::collections::BTreeMap;

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
        self.rec_find_type_with_depth(name, &RecursionDepth::new())
    }
    fn rec_find_type_with_depth(&self, name: &str, depth: &RecursionDepth) -> Result<&Type> {
        let _guard = depth.guard()?;
        let t = self.find_type(name)?;
        match t.as_ref() {
            TypeInner::Var(id) => self.rec_find_type_with_depth(id, depth),
            _ => Ok(t),
        }
    }
    pub fn trace_type<'a>(&'a self, t: &'a Type) -> Result<Type> {
        self.trace_type_with_depth(t, &RecursionDepth::new())
    }
    fn trace_type_with_depth<'a>(&'a self, t: &'a Type, depth: &RecursionDepth) -> Result<Type> {
        let _guard = depth.guard()?;
        match t.as_ref() {
            TypeInner::Var(id) => self.trace_type_with_depth(self.find_type(id)?, depth),
            TypeInner::Knot(ref id) => {
                self.trace_type_with_depth(&crate::types::internal::find_type(id).unwrap(), depth)
            }
            _ => Ok(t.clone()),
        }
    }
    pub fn as_func<'a>(&'a self, t: &'a Type) -> Result<&'a Function> {
        self.as_func_with_depth(t, &RecursionDepth::new())
    }
    fn as_func_with_depth<'a>(&'a self, t: &'a Type, depth: &RecursionDepth) -> Result<&'a Function> {
        let _guard = depth.guard()?;
        match t.as_ref() {
            TypeInner::Func(f) => Ok(f),
            TypeInner::Var(id) => self.as_func_with_depth(self.find_type(id)?, depth),
            _ => Err(Error::msg(format!("not a function type: {t}"))),
        }
    }
    pub fn as_service<'a>(&'a self, t: &'a Type) -> Result<&'a [(String, Type)]> {
        self.as_service_with_depth(t, &RecursionDepth::new())
    }
    fn as_service_with_depth<'a>(
        &'a self,
        t: &'a Type,
        depth: &RecursionDepth,
    ) -> Result<&'a [(String, Type)]> {
        let _guard = depth.guard()?;
        match t.as_ref() {
            TypeInner::Service(s) => Ok(s),
            TypeInner::Var(id) => self.as_service_with_depth(self.find_type(id)?, depth),
            TypeInner::Class(_, ty) => self.as_service_with_depth(ty, depth),
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
        depth: &RecursionDepth,
    ) -> Result<bool> {
        let _guard = depth.guard()?;
        let result = match res.get(id) {
            None => {
                res.insert(id, None);
                let t = self.find_type(id)?;
                let result = match t.as_ref() {
                    TypeInner::Record(fs) => {
                        for f in fs {
                            // Assume env only comes from type table, f.ty is either primitive or var.
                            if let TypeInner::Var(f_id) = f.ty.as_ref() {
                                if self.is_empty(res, f_id, depth)? {
                                    res.insert(id, Some(true));
                                    return Ok(true);
                                }
                            }
                        }
                        false
                    }
                    TypeInner::Var(id) => self.is_empty(res, id, depth)?,
                    _ => false,
                };
                res.insert(id, Some(result));
                result
            }
            Some(None) => {
                res.insert(id, Some(true));
                true
            }
            Some(Some(b)) => *b,
        };
        Ok(result)
    }
    pub fn replace_empty(&mut self) -> Result<()> {
        let mut res = BTreeMap::new();
        for name in self.0.keys() {
            self.is_empty(&mut res, name, &RecursionDepth::new())?;
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
}
impl std::fmt::Display for TypeEnv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (k, v) in &self.0 {
            writeln!(f, "type {k} = {v}")?;
        }
        Ok(())
    }
}
