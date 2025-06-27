use crate::{Error, Result};
use candid::types::{
    syntax::{IDLMergedProg, IDLType},
    Type, TypeEnv, TypeInner,
};
use std::collections::{BTreeMap, BTreeSet};

/// Select a subset of methods from an actor.
pub fn project_methods(
    env: &TypeEnv,
    actor: &Option<Type>,
    mut methods: Vec<String>,
) -> Result<Type> {
    let actor = actor.as_ref().ok_or_else(|| Error::msg("no actor"))?;
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
        return Err(Error::msg(format!("methods not found: {:?}", methods)));
    }
    Ok(TypeInner::Service(filtered).into())
}

/// Same as chase_actor, with seen set as part of the type. Used for chasing type names from type definitions.
pub fn chase_type<'a>(
    seen: &mut BTreeSet<&'a str>,
    res: &mut Vec<&'a str>,
    prog: &'a IDLMergedProg,
    t: &'a IDLType,
) -> Result<()> {
    use IDLType::*;
    match t {
        VarT(id) => {
            if seen.insert(id) {
                let t = prog.find_type(id).map_err(Error::msg)?;
                chase_type(seen, res, prog, t)?;
                res.push(id);
            }
        }
        OptT(ty) | VecT(ty) => chase_type(seen, res, prog, ty)?,
        RecordT(fs) | VariantT(fs) => {
            for f in fs.iter() {
                chase_type(seen, res, prog, &f.typ)?;
            }
        }
        FuncT(f) => {
            let args = f.args.iter().map(|arg| &arg.typ);
            for ty in args.clone().chain(f.rets.iter()) {
                chase_type(seen, res, prog, ty)?;
            }
        }
        ServT(bindings) => {
            for binding in bindings.iter() {
                chase_type(seen, res, prog, &binding.typ)?;
            }
        }
        ClassT(args, t) => {
            for arg in args.iter() {
                chase_type(seen, res, prog, &arg.typ)?;
            }
            chase_type(seen, res, prog, t)?;
        }
        _ => (),
    }
    Ok(())
}

/// Gather type definitions mentioned in actor, return the non-recursive type names in topological order.
/// Recursive types can appear in any order.
pub fn chase_actor<'a>(prog: &'a IDLMergedProg, actor: &'a IDLType) -> Result<Vec<&'a str>> {
    let mut seen = BTreeSet::new();
    let mut res = Vec::new();
    chase_type(&mut seen, &mut res, prog, actor)?;
    Ok(res)
}
/// Given an actor, return a map from variable names to the (methods, arg) that use them.
pub fn chase_def_use(prog: &IDLMergedProg) -> Result<BTreeMap<String, Vec<String>>> {
    let mut res = BTreeMap::new();
    let actor = prog.actor.as_ref().ok_or_else(|| Error::msg("no actor"))?;
    let actor = prog.trace_type(&actor.typ).map_err(Error::msg)?;
    if let IDLType::ClassT(args, _) = &actor {
        for (i, arg) in args.iter().enumerate() {
            let mut used = Vec::new();
            chase_type(&mut BTreeSet::new(), &mut used, prog, &arg.typ)?;
            for var in used {
                res.entry(var.to_string())
                    .or_insert_with(Vec::new)
                    .push(format!("init.arg{}", i));
            }
        }
    }
    for binding in prog.service_methods(&actor).map_err(Error::msg)? {
        let func = prog.as_func(&binding.typ).map_err(Error::msg)?;
        for (i, arg) in func.args.iter().enumerate() {
            let mut used = Vec::new();
            chase_type(&mut BTreeSet::new(), &mut used, prog, &arg.typ)?;
            for var in used {
                res.entry(var.to_string())
                    .or_insert_with(Vec::new)
                    .push(format!("{}.arg{}", binding.id, i));
            }
        }
        for (i, arg) in func.rets.iter().enumerate() {
            let mut used = Vec::new();
            chase_type(&mut BTreeSet::new(), &mut used, prog, arg)?;
            for var in used {
                res.entry(var.to_string())
                    .or_insert_with(Vec::new)
                    .push(format!("{}.ret{}", binding.id, i));
            }
        }
    }
    Ok(res)
}

pub fn chase_types<'a>(prog: &'a IDLMergedProg, tys: &'a [IDLType]) -> Result<Vec<&'a str>> {
    let mut seen = BTreeSet::new();
    let mut res = Vec::new();
    for t in tys.iter() {
        chase_type(&mut seen, &mut res, prog, t)?;
    }
    Ok(res)
}

/// Given a `def_list` produced by the `chase_actor` function, infer which types are recursive
pub fn infer_rec<'a>(
    _prog: &'a IDLMergedProg,
    def_list: &'a [&'a str],
) -> Result<BTreeSet<&'a str>> {
    let mut seen = BTreeSet::new();
    let mut res = BTreeSet::new();
    fn go<'a>(
        seen: &mut BTreeSet<&'a str>,
        res: &mut BTreeSet<&'a str>,
        _env: &'a IDLMergedProg,
        t: &'a IDLType,
    ) -> Result<()> {
        use IDLType::*;
        match t {
            VarT(id) => {
                if seen.insert(id) {
                    res.insert(id);
                }
            }
            OptT(ty) | VecT(ty) => go(seen, res, _env, ty)?,
            RecordT(fs) | VariantT(fs) => {
                for f in fs.iter() {
                    go(seen, res, _env, &f.typ)?;
                }
            }
            FuncT(f) => {
                let args = f.args.iter().map(|arg| &arg.typ);
                for ty in args.clone().chain(f.rets.iter()) {
                    go(seen, res, _env, ty)?;
                }
            }
            ServT(ms) => {
                for binding in ms.iter() {
                    go(seen, res, _env, &binding.typ)?;
                }
            }
            ClassT(args, t) => {
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
        let t = _prog.find_type(var).unwrap();
        go(&mut seen, &mut res, _prog, t)?;
        seen.insert(var);
    }
    Ok(res)
}
