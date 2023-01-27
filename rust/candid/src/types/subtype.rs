use super::internal::{find_type, Field, Label, Type, TypeInner};
use crate::parser::typing::TypeEnv;
use crate::{Error, Result};
use anyhow::Context;
use std::collections::{HashMap, HashSet};

pub type Gamma = HashSet<(Type, Type)>;

/// Check if t1 <: t2
pub fn subtype(gamma: &mut Gamma, env: &TypeEnv, t1: &Type, t2: &Type) -> Result<()> {
    use TypeInner::*;
    if t1 == t2 {
        return Ok(());
    }
    if matches!(t1.as_ref(), Var(_) | Knot(_)) || matches!(t2.as_ref(), Var(_) | Knot(_)) {
        if !gamma.insert((t1.clone(), t2.clone())) {
            return Ok(());
        }
        let res = match (t1.as_ref(), t2.as_ref()) {
            (Var(id), _) => subtype(gamma, env, env.rec_find_type(id).unwrap(), t2),
            (_, Var(id)) => subtype(gamma, env, t1, env.rec_find_type(id).unwrap()),
            (Knot(id), _) => subtype(gamma, env, &find_type(id).unwrap(), t2),
            (_, Knot(id)) => subtype(gamma, env, t1, &find_type(id).unwrap()),
            (_, _) => unreachable!(),
        };
        if res.is_err() {
            gamma.remove(&(t1.clone(), t2.clone()));
        }
        return res;
    }
    match (t1.as_ref(), t2.as_ref()) {
        (_, Reserved) => Ok(()),
        (Empty, _) => Ok(()),
        (Nat, Int) => Ok(()),
        (Vec(ty1), Vec(ty2)) => subtype(gamma, env, ty1, ty2),
        (Null, Opt(_)) => Ok(()),
        (Opt(ty1), Opt(ty2)) if subtype(gamma, env, ty1, ty2).is_ok() => Ok(()),
        (_, Opt(ty2))
            if subtype(gamma, env, t1, ty2).is_ok()
                && !matches!(env.trace_type(ty2)?.as_ref(), Null | Reserved | Opt(_)) =>
        {
            Ok(())
        }
        (_, Opt(_)) => {
            #[cfg(not(feature = "mute_warnings"))]
            eprintln!("FIX ME! {t1} <: {t2} via special opt rule.\nThis means the sender and receiver type has diverged, and can cause data loss.");
            Ok(())
        }
        (Record(fs1), Record(fs2)) => {
            let fields: HashMap<_, _> = fs1.iter().map(|Field { id, ty }| (id, ty)).collect();
            for Field { id, ty: ty2 } in fs2.iter() {
                match fields.get(id) {
                    Some(ty1) => subtype(gamma, env, ty1, ty2).with_context(|| format!("Record field {id}: {ty1} is not a subtype of {ty2}"))?,
                    None => subtype(gamma, env, &Opt(Empty.into()).into(), ty2).map_err(|_| anyhow::anyhow!("Record field {id}: {ty2} is only in the expected type and is not of opt or reserved type"))?,
                }
            }
            Ok(())
        }
        (Variant(fs1), Variant(fs2)) => {
            let fields: HashMap<_, _> = fs2.iter().map(|Field { id, ty }| (id, ty)).collect();
            for Field { id, ty: ty1 } in fs1.iter() {
                match fields.get(id) {
                    Some(ty2) => subtype(gamma, env, ty1, ty2).with_context(|| {
                        format!("Variant field {id}: {ty1} is not a subtype of {ty2}")
                    })?,
                    None => {
                        return Err(Error::msg(format!(
                            "Variant field {id} not found in the expected type"
                        )))
                    }
                }
            }
            Ok(())
        }
        (Service(ms1), Service(ms2)) => {
            let meths: HashMap<_, _> = ms1.iter().map(|(name, ty)| (name, ty)).collect();
            for (name, ty2) in ms2.iter() {
                match meths.get(name) {
                    Some(ty1) => subtype(gamma, env, ty1, ty2).with_context(|| {
                        format!("Method {name}: {ty1} is not a subtype of {ty2}")
                    })?,
                    None => {
                        return Err(Error::msg(format!(
                            "Method {name} is only in the expected type"
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
            subtype(gamma, env, &args2, &args1).context("Subtype fails at function input type")?;
            subtype(gamma, env, &rets1, &rets2).context("Subtype fails at function return type")?;
            Ok(())
        }
        // This only works in the first order case, but service constructor only appears at the top level according to the spec.
        (Class(_, t), _) => subtype(gamma, env, t, t2),
        (_, Class(_, t)) => subtype(gamma, env, t1, t),
        (Unknown, _) => unreachable!(),
        (_, Unknown) => unreachable!(),
        (_, _) => Err(Error::msg(format!("{t1} is not a subtype of {t2}"))),
    }
}

fn to_tuple(args: &[Type]) -> Type {
    TypeInner::Record(
        args.iter()
            .enumerate()
            .map(|(i, ty)| Field {
                id: Label::Id(i as u32).into(),
                ty: ty.clone(),
            })
            .collect(),
    )
    .into()
}
