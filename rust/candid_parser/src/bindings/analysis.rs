use crate::{Error, Result};
use candid::types::{Type, TypeEnv, TypeInner};
use std::collections::{BTreeMap, BTreeSet};

/// Select a subset of methods from an actor.
pub fn project_methods(
    env: &TypeEnv,
    actor: &Option<Type>,
    mut methods: Vec<String>,
) -> Result<Type> {
    let actor = actor
        .as_ref()
        .ok_or_else(|| Error::Custom(anyhow::anyhow!("no actor")))?;
    let service = env.as_service(actor)?;
    let filtered = service
        .iter()
        .filter(|(name, _)| {
            if let Some(idx) = methods.iter().position(|m| m == name) {
                methods.swap_remove(idx);
                true
            } else {
                false
            }
        })
        .cloned()
        .collect();
    if !methods.is_empty() {
        return Err(Error::Custom(anyhow::anyhow!(
            "methods not found: {:?}",
            methods
        )));
    }
    Ok(TypeInner::Service(filtered).into())
}

/// Same as chase_actor, with seen set as part of the type. Used for chasing type names from type definitions.
pub fn chase_type<'a>(
    seen: &mut BTreeSet<&'a str>,
    res: &mut Vec<&'a str>,
    env: &'a TypeEnv,
    t: &'a Type,
) -> Result<()> {
    use TypeInner::*;
    match t.as_ref() {
        Var(id) => {
            if seen.insert(id) {
                let t = env.find_type(id)?;
                chase_type(seen, res, env, t)?;
                res.push(id);
            }
        }
        Opt(ty) | Vec(ty) => chase_type(seen, res, env, ty)?,
        Record(fs) | Variant(fs) => {
            for f in fs.iter() {
                chase_type(seen, res, env, &f.ty)?;
            }
        }
        Func(f) => {
            let args = f.args.iter().map(|arg| &arg.typ);
            for ty in args.clone().chain(f.rets.iter()) {
                chase_type(seen, res, env, ty)?;
            }
        }
        Service(ms) => {
            for (_, ty) in ms.iter() {
                chase_type(seen, res, env, ty)?;
            }
        }
        Class(args, t) => {
            for arg in args.iter() {
                chase_type(seen, res, env, &arg.typ)?;
            }
            chase_type(seen, res, env, t)?;
        }
        _ => (),
    }
    Ok(())
}

/// Gather type definitions mentioned in actor, return the non-recursive type names in topological order.
/// Recursive types can appear in any order.
pub fn chase_actor<'a>(env: &'a TypeEnv, actor: &'a Type) -> Result<Vec<&'a str>> {
    let mut seen = BTreeSet::new();
    let mut res = Vec::new();
    chase_type(&mut seen, &mut res, env, actor)?;
    Ok(res)
}
/// Given an actor, return a map from variable names to the (methods, arg) that use them.
pub fn chase_def_use<'a>(
    env: &'a TypeEnv,
    actor: &'a Type,
) -> Result<BTreeMap<String, Vec<String>>> {
    let mut res = BTreeMap::new();
    let actor = env.trace_type(actor)?;
    if let TypeInner::Class(args, _) = actor.as_ref() {
        for (i, arg) in args.iter().enumerate() {
            let mut used = Vec::new();
            chase_type(&mut BTreeSet::new(), &mut used, env, &arg.typ)?;
            for var in used {
                res.entry(var.to_string())
                    .or_insert_with(Vec::new)
                    .push(format!("init.arg{}", i));
            }
        }
    }
    for (id, ty) in env.as_service(&actor)? {
        let func = env.as_func(ty)?;
        for (i, arg) in func.args.iter().enumerate() {
            let mut used = Vec::new();
            chase_type(&mut BTreeSet::new(), &mut used, env, &arg.typ)?;
            for var in used {
                res.entry(var.to_string())
                    .or_insert_with(Vec::new)
                    .push(format!("{}.arg{}", id, i));
            }
        }
        for (i, arg) in func.rets.iter().enumerate() {
            let mut used = Vec::new();
            chase_type(&mut BTreeSet::new(), &mut used, env, arg)?;
            for var in used {
                res.entry(var.to_string())
                    .or_insert_with(Vec::new)
                    .push(format!("{}.ret{}", id, i));
            }
        }
    }
    Ok(res)
}

pub fn chase_types<'a>(env: &'a TypeEnv, tys: &'a [Type]) -> Result<Vec<&'a str>> {
    let mut seen = BTreeSet::new();
    let mut res = Vec::new();
    for t in tys.iter() {
        chase_type(&mut seen, &mut res, env, t)?;
    }
    Ok(res)
}

/// Given a `def_list` produced by the `chase_actor` function, infer which types are recursive
pub fn infer_rec<'a>(_env: &'a TypeEnv, def_list: &'a [&'a str]) -> Result<BTreeSet<&'a str>> {
    let mut seen = BTreeSet::new();
    let mut res = BTreeSet::new();
    fn go<'a>(
        seen: &mut BTreeSet<&'a str>,
        res: &mut BTreeSet<&'a str>,
        _env: &'a TypeEnv,
        t: &'a Type,
    ) -> Result<()> {
        use TypeInner::*;
        match t.as_ref() {
            Var(id) => {
                if seen.insert(id) {
                    res.insert(id);
                }
            }
            Opt(ty) | Vec(ty) => go(seen, res, _env, ty)?,
            Record(fs) | Variant(fs) => {
                for f in fs.iter() {
                    go(seen, res, _env, &f.ty)?;
                }
            }
            Func(f) => {
                let args = f.args.iter().map(|arg| &arg.typ);
                for ty in args.clone().chain(f.rets.iter()) {
                    go(seen, res, _env, ty)?;
                }
            }
            Service(ms) => {
                for (_, ty) in ms.iter() {
                    go(seen, res, _env, ty)?;
                }
            }
            Class(args, t) => {
                for arg in args.iter() {
                    go(seen, res, _env, &arg.typ)?;
                }
                go(seen, res, _env, t)?;
            }
            _ => (),
        }
        Ok(())
    }
    for var in def_list.iter() {
        let t = _env.0.get(*var).unwrap();
        go(&mut seen, &mut res, _env, t)?;
        seen.insert(var);
    }
    Ok(res)
}
