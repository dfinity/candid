use super::internal::{find_type, Field, Label, Type};
use crate::parser::typing::TypeEnv;
use crate::{Error, Result};
use anyhow::Context;
use std::collections::{HashMap, HashSet};

pub type Gamma = HashSet<(Type, Type)>;

/// Check if t1 <: t2
pub fn subtype(
    gamma: &mut Gamma,
    env1: &TypeEnv,
    t1: &Type,
    env2: &TypeEnv,
    t2: &Type,
) -> Result<()> {
    use Type::*;
    if t1 == t2 {
        return Ok(());
    }
    if matches!(t1, Var(_) | Knot(_)) || matches!(t2, Var(_) | Knot(_)) {
        if !gamma.insert((t1.clone(), t2.clone())) {
            return Ok(());
        }
        let res = match (t1, t2) {
            (Var(id), _) => subtype(gamma, env1, env1.rec_find_type(id).unwrap(), env2, t2),
            (_, Var(id)) => subtype(gamma, env1, t1, env2, env2.rec_find_type(id).unwrap()),
            (Knot(id), _) => subtype(gamma, env1, &find_type(id).unwrap(), env2, t2),
            (_, Knot(id)) => subtype(gamma, env1, t1, env2, &find_type(id).unwrap()),
            (_, _) => unreachable!(),
        };
        if res.is_err() {
            gamma.remove(&(t1.clone(), t2.clone()));
        }
        return res;
    }
    match (t1, t2) {
        (_, Reserved) => Ok(()),
        (Empty, _) => Ok(()),
        (Nat, Int) => Ok(()),
        (Vec(ty1), Vec(ty2)) => subtype(gamma, env1, ty1, env2, ty2),
        (Null, Opt(_)) => Ok(()),
        (Opt(ty1), Opt(ty2)) if subtype(gamma, env1, ty1, env2, ty2).is_ok() => Ok(()),
        (t1, Opt(ty2))
            if subtype(gamma, env1, t1, env2, ty2).is_ok()
                && !matches!(env2.trace_type(ty2).unwrap(), Null | Reserved | Opt(_)) =>
        {
            Ok(())
        }
        (t1, Opt(_)) => {
            eprintln!("{} <: {} via special opt rule", t1, t2);
            Ok(())
        }
        (Record(fs1), Record(fs2)) => {
            let fields: HashMap<_, _> = fs1.iter().map(|Field { id, ty }| (id, ty)).collect();
            for Field { id, ty: ty2 } in fs2.iter() {
                match fields.get(id) {
                    Some(ty1) => subtype(gamma, env1, ty1, env2, ty2).with_context(|| format!("Record field {}: {} is not a subtype of {}", id, ty1, ty2))?,
                    None => subtype(gamma, env1, &Opt(Box::new(Empty)), env2, ty2).map_err(|_| anyhow::anyhow!("Record field {} : {} is only in the expected type and is not of opt, reserved or null type", id, ty2))?,
                }
            }
            Ok(())
        }
        (Variant(fs1), Variant(fs2)) => {
            let fields: HashMap<_, _> = fs2.iter().map(|Field { id, ty }| (id, ty)).collect();
            for Field { id, ty: ty1 } in fs1.iter() {
                match fields.get(id) {
                    Some(ty2) => subtype(gamma, env1, ty1, env2, ty2).with_context(|| {
                        format!("Variant field {}: {} is not a subtype of {}", id, ty1, ty2)
                    })?,
                    None => {
                        return Err(Error::msg(format!(
                            "Variant field {} not found in the expected type",
                            id
                        )))
                    }
                }
            }
            Ok(())
        }
        (Service(ms1), Service(ms2)) => {
            let meths: HashMap<_, _> = ms2.iter().map(|(name, ty)| (name, ty)).collect();
            for (name, ty1) in ms1.iter() {
                match meths.get(name) {
                    Some(ty2) => subtype(gamma, env1, ty1, env2, ty2).with_context(|| {
                        format!("Method {}: {} is not a subtype of {}", name, ty1, ty2)
                    })?,
                    None => {
                        return Err(Error::msg(format!(
                            "Method {} not found in expected type",
                            name
                        )))
                    }
                }
            }
            Ok(())
        }
        (Func(f1), Func(f2)) => {
            let m1: HashSet<_> = f1.modes.iter().collect();
            let m2: HashSet<_> = f2.modes.iter().collect();
            if m1 != m2 {
                return Err(Error::msg("Function mode mismatch"));
            }
            let args1 = to_tuple(&f1.args);
            let args2 = to_tuple(&f2.args);
            let rets1 = to_tuple(&f1.rets);
            let rets2 = to_tuple(&f2.rets);
            subtype(gamma, env2, &args2, env1, &args1)?;
            subtype(gamma, env1, &rets1, env2, &rets2)?;
            Ok(())
        }
        (Class(_, _), Class(_, _)) => unreachable!(),
        (Unknown, _) => unreachable!(),
        (_, Unknown) => unreachable!(),
        (_, _) => Err(Error::msg(format!("{} is not a subtype of {}", t1, t2))),
    }
}

fn to_tuple(args: &[Type]) -> Type {
    Type::Record(
        args.iter()
            .enumerate()
            .map(|(i, ty)| Field {
                id: Label::Id(i as u32),
                ty: ty.clone(),
            })
            .collect(),
    )
}
