use crate::types::internal::TypeKey;
use crate::types::{Function, Type, TypeInner};
use crate::{Error, Result};
use foldhash::fast::FixedState;
use hashbrown::HashMap;

pub type TypeMap<V> = HashMap<TypeKey, V, FixedState>;

#[derive(Debug, Clone, Default)]
pub struct TypeEnv(pub TypeMap<Type>);

pub trait SortedIter<T> {
    /// Creates an iterator that iterates over the elements in the order of keys.
    ///
    /// The implementation collects elements into a temporary vector and sorts the vector.
    fn to_sorted_iter<'a>(&'a self) -> impl Iterator<Item = (&'a TypeKey, &'a T)>
    where
        T: 'a;
}

impl<T> SortedIter<T> for TypeMap<T> {
    fn to_sorted_iter<'a>(&'a self) -> impl Iterator<Item = (&'a TypeKey, &'a T)>
    where
        T: 'a,
    {
        let mut vec: Vec<_> = self.iter().collect();
        vec.sort_unstable_by_key(|elem| elem.0);
        vec.into_iter()
    }
}

impl TypeEnv {
    pub fn new() -> Self {
        TypeEnv(TypeMap::default())
    }

    pub fn merge<'a>(&'a mut self, env: &TypeEnv) -> Result<&'a mut Self> {
        for (k, v) in env.0.iter() {
            let entry = self.0.entry(k.clone()).or_insert_with(|| v.clone());
            if *entry != *v {
                return Err(Error::msg("inconsistent binding"));
            }
        }
        Ok(self)
    }
    pub fn merge_type(&mut self, env: TypeEnv, ty: Type) -> Type {
        let tau: TypeMap<TypeKey> = env
            .0
            .keys()
            .filter(|k| self.0.contains_key(*k))
            .map(|k| (k.clone(), format!("{k}/1").into()))
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
    pub fn find_type(&self, key: &TypeKey) -> Result<&Type> {
        match self.0.get(key) {
            None => Err(Error::msg(format!("Unbound type identifier {key}"))),
            Some(t) => Ok(t),
        }
    }

    pub fn rec_find_type(&self, name: &TypeKey) -> Result<&Type> {
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
        res: &mut HashMap<&'a TypeKey, Option<bool>, FixedState>,
        id: &'a TypeKey,
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
        let mut res = HashMap::default();
        for key in self.0.keys() {
            self.is_empty(&mut res, key)?;
        }
        let ids: Vec<_> = res
            .into_iter()
            .filter(|(_, v)| matches!(v, Some(true)))
            .map(|(id, _)| id.to_owned())
            .collect();
        for id in ids {
            self.0.insert(id, TypeInner::Empty.into());
        }
        Ok(())
    }
}

impl std::fmt::Display for TypeEnv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (k, v) in self.0.to_sorted_iter() {
            writeln!(f, "type {k} = {v}")?;
        }
        Ok(())
    }
}
