use super::internal::{find_type, Field, Label, Type};
use crate::parser::typing::TypeEnv;
use std::collections::{HashMap, HashSet};

pub type Gamma = HashSet<(Type, Type)>;

/// Check if t1 <: t2
pub fn subtype(gamma: &mut Gamma, env1: &TypeEnv, t1: &Type, env2: &TypeEnv, t2: &Type) -> bool {
    use Type::*;
    if t1 == t2 {
        return true;
    }
    if matches!(t1, Var(_) | Knot(_) | Blob) || matches!(t2, Var(_) | Knot(_) | Blob) {
        if !gamma.insert((t1.clone(), t2.clone())) {
            return true;
        }
        let res = match (t1, t2) {
            (Var(id), _) => subtype(gamma, env1, env1.rec_find_type(id).unwrap(), env2, t2),
            (_, Var(id)) => subtype(gamma, env1, t1, env2, env2.rec_find_type(id).unwrap()),
            (Knot(id), _) => subtype(gamma, env1, &find_type(id).unwrap(), env2, t2),
            (_, Knot(id)) => subtype(gamma, env1, t1, env2, &find_type(id).unwrap()),
            (Blob, _) => subtype(gamma, env1, &Vec(Box::new(Nat8)), env2, t2),
            (_, Blob) => subtype(gamma, env1, t1, env2, &Vec(Box::new(Nat8))),
            (_, _) => unreachable!(),
        };
        if !res {
            gamma.remove(&(t1.clone(), t2.clone()));
        }
        return res;
    }
    match (t1, t2) {
        (_, Reserved) => true,
        (Empty, _) => true,
        (Nat, Int) => true,
        (Vec(ty1), Vec(ty2)) => subtype(gamma, env1, ty1, env2, ty2),
        (Null, Opt(_)) => true,
        (Opt(ty1), Opt(ty2)) if subtype(gamma, env1, ty1, env2, ty2) => true,
        (t1, Opt(ty2))
            if subtype(gamma, env1, t1, env2, ty2)
                && !matches!(env2.trace_type(ty2).unwrap(), Null | Reserved | Opt(_)) =>
        {
            true
        }
        (t1, Opt(_)) => {
            eprintln!("{} <: {} via special opt rule", t1, t2);
            true
        }
        (Record(fs1), Record(fs2)) => {
            let fields: HashMap<_, _> = fs1.iter().map(|Field { id, ty }| (id, ty)).collect();
            fs2.iter()
                .all(|Field { id, ty: ty2 }| match fields.get(id) {
                    Some(ty1) => subtype(gamma, env1, ty1, env2, ty2),
                    None => subtype(gamma, env1, &Opt(Box::new(Empty)), env2, ty2),
                })
        }
        (Variant(fs1), Variant(fs2)) => {
            let fields: HashMap<_, _> = fs2.iter().map(|Field { id, ty }| (id, ty)).collect();
            fs1.iter()
                .all(|Field { id, ty: ty1 }| match fields.get(id) {
                    Some(ty2) => subtype(gamma, env1, ty1, env2, ty2),
                    None => false,
                })
        }
        (Service(ms1), Service(ms2)) => {
            let meths: HashMap<_, _> = ms2.iter().map(|(name, ty)| (name, ty)).collect();
            ms1.iter().all(|(name, ty1)| match meths.get(name) {
                Some(ty2) => subtype(gamma, env1, ty1, env2, ty2),
                None => false,
            })
        }
        (Func(f1), Func(f2)) => {
            let m1: HashSet<_> = f1.modes.iter().collect();
            let m2: HashSet<_> = f2.modes.iter().collect();
            if m1 != m2 {
                return false;
            }
            let args1 = to_tuple(&f1.args);
            let args2 = to_tuple(&f2.args);
            let rets1 = to_tuple(&f1.rets);
            let rets2 = to_tuple(&f2.rets);
            subtype(gamma, env2, &args2, env1, &args1) && subtype(gamma, env1, &rets1, env2, &rets2)
        }
        (Class(_, _), Class(_, _)) => unreachable!(),
        (Unknown, _) => unreachable!(),
        (_, Unknown) => unreachable!(),
        (_, _) => false,
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
