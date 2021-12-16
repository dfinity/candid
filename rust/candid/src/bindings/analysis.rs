use crate::parser::typing::TypeEnv;
use crate::types::Type;
use crate::Result;
use std::collections::BTreeSet;

/// Same as chase_actor, with seen set as part of the type. Used for chasing type names from type definitions.
pub fn chase_type<'a>(
    seen: &mut BTreeSet<&'a str>,
    res: &mut Vec<&'a str>,
    env: &'a TypeEnv,
    t: &'a Type,
) -> Result<()> {
    use Type::*;
    match t {
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
            for ty in f.args.iter().chain(f.rets.iter()) {
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
                chase_type(seen, res, env, arg)?;
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

pub fn chase_types<'a>(env: &'a TypeEnv, tys: &'a [Type]) -> Result<Vec<&'a str>> {
    let mut seen = BTreeSet::new();
    let mut res = Vec::new();
    for t in tys.iter() {
        chase_type(&mut seen, &mut res, env, t)?;
    }
    Ok(res)
}

/// Given a `def_list` produced by the `chase_actor` function, infer which types are recursive
pub fn infer_rec<'a>(env: &'a TypeEnv, def_list: &'a [&'a str]) -> Result<BTreeSet<&'a str>> {
    let mut seen = BTreeSet::new();
    let mut res = BTreeSet::new();
    fn go<'a>(
        seen: &mut BTreeSet<&'a str>,
        res: &mut BTreeSet<&'a str>,
        env: &'a TypeEnv,
        t: &'a Type,
    ) -> Result<()> {
        use Type::*;
        match t {
            Var(id) => {
                if seen.insert(id) {
                    res.insert(id);
                }
            }
            Opt(ty) | Vec(ty) => go(seen, res, env, ty)?,
            Record(fs) | Variant(fs) => {
                for f in fs.iter() {
                    go(seen, res, env, &f.ty)?;
                }
            }
            Func(f) => {
                for ty in f.args.iter().chain(f.rets.iter()) {
                    go(seen, res, env, ty)?;
                }
            }
            Service(ms) => {
                for (_, ty) in ms.iter() {
                    go(seen, res, env, ty)?;
                }
            }
            Class(args, t) => {
                for arg in args.iter() {
                    go(seen, res, env, arg)?;
                }
                go(seen, res, env, t)?;
            }
            _ => (),
        }
        Ok(())
    }
    for var in def_list.iter() {
        let t = env.0.get(*var).unwrap();
        go(&mut seen, &mut res, env, t)?;
        seen.insert(var);
    }
    Ok(res)
}
