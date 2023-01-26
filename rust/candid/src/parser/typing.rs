use super::types::*;
use crate::types::{Field, Function, Type, TypeInner};
use crate::{pretty_parse, Error, Result};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

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
    pub fn merge_type(&mut self, env: TypeEnv, ty: Type) -> Type {
        let tau: BTreeMap<String, String> = env
            .0
            .keys()
            .filter(|k| self.0.contains_key(*k))
            .map(|k| (k.clone(), format!("{}/1", k)))
            .collect();
        for (k, t) in env.0.into_iter() {
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
            None => Err(Error::msg(format!("Unbound type identifier {}", name))),
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
            _ => Err(Error::msg(format!("not a function type: {}", t))),
        }
    }
    pub fn as_service<'a>(&'a self, t: &'a Type) -> Result<&'a [(String, Type)]> {
        match t.as_ref() {
            TypeInner::Service(s) => Ok(s),
            TypeInner::Var(id) => self.as_service(self.find_type(id)?),
            TypeInner::Class(_, ty) => self.as_service(ty),
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
    fn go<'a>(
        &'a self,
        seen: &mut BTreeSet<&'a str>,
        res: &mut BTreeSet<&'a str>,
        t: &'a Type,
    ) -> Result<()> {
        if !res.is_empty() {
            return Ok(());
        }
        match t.as_ref() {
            TypeInner::Record(fs) => {
                for f in fs.iter() {
                    self.go(seen, res, &f.ty)?;
                }
            }
            TypeInner::Var(id) => {
                if seen.insert(id) {
                    let t = self.find_type(id)?;
                    self.go(seen, res, t)?;
                    seen.remove(&id.as_str());
                } else {
                    *res = seen.clone();
                }
            }
            _ => (),
        }
        Ok(())
    }
    fn check_empty(&self) -> Result<BTreeSet<&str>> {
        let mut res = BTreeSet::new();
        for (name, t) in self.0.iter() {
            let mut seen: BTreeSet<&str> = BTreeSet::new();
            let mut local_res = BTreeSet::new();
            seen.insert(name);
            self.go(&mut seen, &mut local_res, t)?;
            res.append(&mut local_res);
        }
        Ok(res)
    }
    #[allow(clippy::needless_collect)]
    pub fn replace_empty(&mut self) -> Result<()> {
        let ids: Vec<_> = self.check_empty()?.iter().map(|x| x.to_string()).collect();
        for id in ids.into_iter() {
            self.0.insert(id, TypeInner::Empty.into());
        }
        Ok(())
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

pub fn check_type(env: &Env, t: &IDLType) -> Result<Type> {
    match t {
        IDLType::PrimT(prim) => Ok(check_prim(prim)),
        IDLType::VarT(id) => {
            env.te.find_type(id)?;
            Ok(TypeInner::Var(id.to_string()).into())
        }
        IDLType::OptT(t) => {
            let t = check_type(env, t)?;
            Ok(TypeInner::Opt(t).into())
        }
        IDLType::VecT(t) => {
            let t = check_type(env, t)?;
            Ok(TypeInner::Vec(t).into())
        }
        IDLType::RecordT(fs) => {
            let fs = check_fields(env, fs)?;
            Ok(TypeInner::Record(fs).into())
        }
        IDLType::VariantT(fs) => {
            let fs = check_fields(env, fs)?;
            Ok(TypeInner::Variant(fs).into())
        }
        IDLType::PrincipalT => Ok(TypeInner::Principal.into()),
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
            Ok(TypeInner::Func(f).into())
        }
        IDLType::ServT(ms) => {
            let ms = check_meths(env, ms)?;
            Ok(TypeInner::Service(ms).into())
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
            id: f.label.clone().into(),
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
        match t.as_ref() {
            TypeInner::Var(id) => {
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
            let duplicate = env.te.0.insert(id.to_string(), TypeInner::Unknown.into());
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
            Ok(Some(TypeInner::Class(args, serv).into()))
        }
        Some(typ) => {
            let t = check_type(env, typ)?;
            env.te.as_service(&t)?;
            Ok(Some(t))
        }
    }
}

fn resolve_path(base: &Path, file: &str) -> PathBuf {
    // TODO use shellexpand to support tilde
    let file = PathBuf::from(file);
    if file.is_absolute() {
        file
    } else {
        base.join(file)
    }
}

fn load_imports(
    is_pretty: bool,
    base: &Path,
    visited: &mut BTreeSet<PathBuf>,
    prog: &IDLProg,
    list: &mut Vec<PathBuf>,
) -> Result<()> {
    for dec in prog.decs.iter() {
        if let Dec::ImportD(file) = dec {
            let path = resolve_path(base, file);
            if visited.insert(path.clone()) {
                let code = std::fs::read_to_string(&path)
                    .map_err(|_| Error::msg(format!("Cannot import {:?}", file)))?;
                let code = if is_pretty {
                    pretty_parse::<IDLProg>(path.to_str().unwrap(), &code)?
                } else {
                    code.parse::<IDLProg>()?
                };
                let base = path.parent().unwrap();
                load_imports(is_pretty, base, visited, &code, list)?;
                list.push(path);
            }
        }
    }
    Ok(())
}

/// Type check IDLProg and adds bindings to type environment. Returns
/// a hash map for the serivce method signatures. This function ignores the imports.
pub fn check_prog(te: &mut TypeEnv, prog: &IDLProg) -> Result<Option<Type>> {
    let mut env = Env { te, pre: false };
    check_decs(&mut env, &prog.decs)?;
    check_actor(&env, &prog.actor)
}

fn check_file_(file: &Path, is_pretty: bool) -> Result<(TypeEnv, Option<Type>)> {
    let base = if file.is_absolute() {
        file.parent().unwrap().to_path_buf()
    } else {
        std::env::current_dir()?
            .join(file)
            .parent()
            .unwrap()
            .to_path_buf()
    };
    let prog =
        std::fs::read_to_string(file).map_err(|_| Error::msg(format!("Cannot open {:?}", file)))?;
    let prog = if is_pretty {
        pretty_parse::<IDLProg>(file.to_str().unwrap(), &prog)?
    } else {
        prog.parse::<IDLProg>()?
    };
    let mut imports = Vec::new();
    load_imports(is_pretty, &base, &mut BTreeSet::new(), &prog, &mut imports)?;
    let mut te = TypeEnv::new();
    let mut env = Env {
        te: &mut te,
        pre: false,
    };
    for import in imports.iter() {
        let code = std::fs::read_to_string(import)?;
        let code = code.parse::<IDLProg>()?;
        check_decs(&mut env, &code.decs)?;
    }
    check_decs(&mut env, &prog.decs)?;
    let actor = check_actor(&env, &prog.actor)?;
    Ok((te, actor))
}

/// Type check did file including the imports.
pub fn check_file(file: &Path) -> Result<(TypeEnv, Option<Type>)> {
    check_file_(file, false)
}
pub fn pretty_check_file(file: &Path) -> Result<(TypeEnv, Option<Type>)> {
    check_file_(file, true)
}
