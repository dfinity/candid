use super::internal::{find_type, Field, Label, Type, TypeInner};
use crate::bindings::candid::pp_args;
use crate::types::TypeEnv;
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
            if f1.modes != f2.modes {
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

/// Check if t1 and t2 are structurally equivalent, ignoring the variable naming differences.
/// Note that this is more strict than `t1 <: t2` and `t2 <: t1`, because of the special opt rule.
pub fn equal(gamma: &mut Gamma, env: &TypeEnv, t1: &Type, t2: &Type) -> Result<()> {
    use TypeInner::*;
    if t1 == t2 {
        return Ok(());
    }
    if matches!(t1.as_ref(), Var(_) | Knot(_)) || matches!(t2.as_ref(), Var(_) | Knot(_)) {
        if !gamma.insert((t1.clone(), t2.clone())) {
            return Ok(());
        }
        let res = match (t1.as_ref(), t2.as_ref()) {
            (Var(id), _) => equal(gamma, env, env.rec_find_type(id).unwrap(), t2),
            (_, Var(id)) => equal(gamma, env, t1, env.rec_find_type(id).unwrap()),
            (Knot(id), _) => equal(gamma, env, &find_type(id).unwrap(), t2),
            (_, Knot(id)) => equal(gamma, env, t1, &find_type(id).unwrap()),
            (_, _) => unreachable!(),
        };
        if res.is_err() {
            gamma.remove(&(t1.clone(), t2.clone()));
        }
        return res;
    }
    match (t1.as_ref(), t2.as_ref()) {
        (Opt(ty1), Opt(ty2)) => equal(gamma, env, ty1, ty2),
        (Vec(ty1), Vec(ty2)) => equal(gamma, env, ty1, ty2),
        (Record(fs1), Record(fs2)) | (Variant(fs1), Variant(fs2)) => {
            assert_length(fs1, fs2, |x| x.to_string()).context("Different field length")?;
            for (f1, f2) in fs1.iter().zip(fs2.iter()) {
                if f1.id != f2.id {
                    return Err(Error::msg(format!(
                        "Field name mismatch: {} and {}",
                        f1.id, f2.id
                    )));
                }
                equal(gamma, env, &f1.ty, &f2.ty).context(format!(
                    "Field {} has different types: {} and {}",
                    f1.id, f1.ty, f2.ty
                ))?;
            }
            Ok(())
        }
        (Service(ms1), Service(ms2)) => {
            assert_length(ms1, ms2, |x| format!("method {} : {}", x.0, x.1))
                .context("Different method length")?;
            for (m1, m2) in ms1.iter().zip(ms2.iter()) {
                if m1.0 != m2.0 {
                    return Err(Error::msg(format!(
                        "Method name mismatch: {} and {}",
                        m1.0, m2.0
                    )));
                }
                equal(gamma, env, &m1.1, &m2.1).context(format!(
                    "Method {} has different types: {} and {}",
                    m1.0, m1.1, m2.1
                ))?;
            }
            Ok(())
        }
        (Func(f1), Func(f2)) => {
            if f1.modes != f2.modes {
                return Err(Error::msg("Function mode mismatch"));
            }
            let args1 = to_tuple(&f1.args);
            let args2 = to_tuple(&f2.args);
            let rets1 = to_tuple(&f1.rets);
            let rets2 = to_tuple(&f2.rets);
            equal(gamma, env, &args1, &args2).context("Mismatch in function input type")?;
            equal(gamma, env, &rets1, &rets2).context("Mismatch in function return type")?;
            Ok(())
        }
        (Class(init1, ty1), Class(init2, ty2)) => {
            let init_1 = to_tuple(init1);
            let init_2 = to_tuple(init2);
            equal(gamma, env, &init_1, &init_2).context(format!(
                "Mismatch in init args: {} and {}",
                pp_args(init1).pretty(80),
                pp_args(init2).pretty(80)
            ))?;
            equal(gamma, env, ty1, ty2)
        }
        (Unknown, _) => unreachable!(),
        (_, Unknown) => unreachable!(),
        (_, _) => Err(Error::msg(format!("{t1} is not equal to {t2}"))),
    }
}

fn assert_length<I, F>(left: &[I], right: &[I], display: F) -> Result<()>
where
    F: Fn(&I) -> String,
    I: Clone + std::hash::Hash + std::cmp::Eq,
{
    let l = left.len();
    let r = right.len();
    if l == r {
        return Ok(());
    }
    let left: HashSet<_> = left.iter().cloned().collect();
    let right: HashSet<_> = right.iter().cloned().collect();
    if l < r {
        let mut diff = right.difference(&left);
        Err(Error::msg(format!(
            "Left side is missing {}",
            display(diff.next().unwrap())
        )))
    } else {
        let mut diff = left.difference(&right);
        Err(Error::msg(format!(
            "Right side is missing {}",
            display(diff.next().unwrap())
        )))
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
