use crate::types::syntax::{Binding, FuncType, IDLArgType, IDLType, PrimType, TypeField};
use crate::types::{ArgType, Field, Function, Type, TypeInner};
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

    pub fn inner_as_idl_type(&self, ty: &TypeInner) -> IDLType {
        match ty {
            TypeInner::Null => IDLType::PrimT(PrimType::Null),
            TypeInner::Bool => IDLType::PrimT(PrimType::Bool),
            TypeInner::Nat => IDLType::PrimT(PrimType::Nat),
            TypeInner::Int => IDLType::PrimT(PrimType::Int),
            TypeInner::Nat8 => IDLType::PrimT(PrimType::Nat8),
            TypeInner::Nat16 => IDLType::PrimT(PrimType::Nat16),
            TypeInner::Nat32 => IDLType::PrimT(PrimType::Nat32),
            TypeInner::Nat64 => IDLType::PrimT(PrimType::Nat64),
            TypeInner::Int8 => IDLType::PrimT(PrimType::Int8),
            TypeInner::Int16 => IDLType::PrimT(PrimType::Int16),
            TypeInner::Int32 => IDLType::PrimT(PrimType::Int32),
            TypeInner::Int64 => IDLType::PrimT(PrimType::Int64),
            TypeInner::Float32 => IDLType::PrimT(PrimType::Float32),
            TypeInner::Float64 => IDLType::PrimT(PrimType::Float64),
            TypeInner::Text => IDLType::PrimT(PrimType::Text),
            TypeInner::Reserved => IDLType::PrimT(PrimType::Reserved),
            TypeInner::Empty => IDLType::PrimT(PrimType::Empty),
            TypeInner::Var(id) => IDLType::VarT(id.to_string()),
            TypeInner::Opt(t) => IDLType::OptT(Box::new(self.as_idl_type(t))),
            TypeInner::Vec(t) => IDLType::VecT(Box::new(self.as_idl_type(t))),
            TypeInner::Record(fields) => IDLType::RecordT(self.fields_to_idl_fields(fields)),
            TypeInner::Variant(fields) => IDLType::VariantT(self.fields_to_idl_fields(fields)),
            TypeInner::Func(func) => IDLType::FuncT(self.func_to_idl_func(func)),
            TypeInner::Service(methods) => IDLType::ServT(self.methods_to_idl_methods(methods)),
            TypeInner::Class(args, t) => IDLType::ClassT(
                self.arg_types_to_idl_arg_types(args),
                Box::new(self.as_idl_type(t)),
            ),
            TypeInner::Principal => IDLType::PrincipalT,
            TypeInner::Knot(id) => {
                let name = id.to_string();
                self.0
                    .get(&name)
                    .unwrap_or_else(|| panic!("Knot type should already be in the env: {:?}", id));
                IDLType::VarT(name)
            }
            TypeInner::Future => IDLType::FutureT,
            TypeInner::Unknown => IDLType::UnknownT,
        }
    }

    pub fn as_idl_type(&self, ty: &Type) -> IDLType {
        self.inner_as_idl_type(ty.as_ref())
    }

    pub fn arg_types_to_idl_arg_types(&self, args: &[ArgType]) -> Vec<IDLArgType> {
        args.iter()
            .map(|arg| IDLArgType {
                typ: self.as_idl_type(&arg.typ),
                name: arg.name.clone(),
            })
            .collect()
    }

    pub fn func_to_idl_func(&self, func: &Function) -> FuncType {
        FuncType {
            modes: func.modes.clone(),
            args: self.arg_types_to_idl_arg_types(&func.args),
            rets: func.rets.iter().map(|arg| self.as_idl_type(arg)).collect(),
        }
    }

    pub fn field_to_idl_field(&self, field: &Field) -> TypeField {
        TypeField {
            label: field.id.as_ref().clone(),
            typ: self.as_idl_type(&field.ty),
            doc_comment: None,
        }
    }

    fn fields_to_idl_fields(&self, fields: &[Field]) -> Vec<TypeField> {
        fields
            .iter()
            .map(|field| self.field_to_idl_field(field))
            .collect()
    }

    fn methods_to_idl_methods(&self, methods: &[(String, Type)]) -> Vec<Binding> {
        methods
            .iter()
            .map(|(id, t)| Binding {
                id: id.clone(),
                typ: self.as_idl_type(t),
                doc_comment: None,
            })
            .collect()
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
