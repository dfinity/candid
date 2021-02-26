use super::internal::{find_type, Field, Label, Type};
use crate::parser::typing::TypeEnv;
use std::collections::{HashMap, HashSet};

/// Check if t1 <: t2
pub fn subtype(env: &TypeEnv, t1: &Type, t2: &Type) -> bool {
    use Type::*;
    if t1 == t2 {
        return true;
    }
    match (t1, t2) {
        (_, Var(id)) => subtype(env, t1, env.rec_find_type(id).unwrap()),
        (Var(id), _) => subtype(env, env.rec_find_type(id).unwrap(), t2),
        (_, Knot(id)) => subtype(env, t1, &find_type(id).unwrap()),
        (Knot(id), _) => subtype(env, &find_type(id).unwrap(), t2),
        (_, Reserved) => true,
        (Empty, _) => true,
        (Nat, Int) => true,
        (Vec(ty1), Vec(ty2)) => subtype(env, ty1, ty2),
        (Null, Opt(_)) => true,
        (Opt(ty1), Opt(ty2)) if subtype(env, ty1, ty2) => true,
        (t1, Opt(ty2)) if subtype(env, t1, ty2) && !subtype(env, &Null, ty2) => true,
        (Opt(ty1), Opt(_ty2)) if !subtype(env, ty1, t2) => {
            eprintln!("{} <: {} via special opt rule", t1, t2);
            true
        }
        (Opt(ty1), Opt(ty2)) if !subtype(env, ty1, ty2) && !subtype(env, &Null, ty1) => {
            eprintln!("{} <: {} via special opt rule", t1, t2);
            true
        }
        (Record(fs1), Record(fs2)) => {
            let fields: HashMap<_, _> = fs1.iter().map(|Field { id, ty }| (id, ty)).collect();
            for Field { id, ty: ty2 } in fs2.iter() {
                match fields.get(id) {
                    Some(ty1) => {
                        if !subtype(env, ty1, ty2) {
                            return false;
                        }
                    }
                    None => {
                        if !subtype(env, &Opt(Box::new(Empty)), ty2) {
                            return false;
                        }
                    }
                }
            }
            true
        }
        (Variant(fs1), Variant(fs2)) => {
            let fields: HashMap<_, _> = fs2.iter().map(|Field { id, ty }| (id, ty)).collect();
            for Field { id, ty: ty1 } in fs1.iter() {
                match fields.get(id) {
                    Some(ty2) => {
                        if !subtype(env, ty1, ty2) {
                            return false;
                        }
                    }
                    None => return false,
                }
            }
            true
        }
        (Service(ms1), Service(ms2)) => {
            let meths: HashMap<_, _> = ms2.iter().map(|(name, ty)| (name, ty)).collect();
            for (name, ty1) in ms1.iter() {
                match meths.get(name) {
                    Some(ty2) => {
                        if !subtype(env, ty1, ty2) {
                            return false;
                        }
                    }
                    None => return false,
                }
            }
            true
        }
        (Func(f1), Func(f2)) => {
            let m1: HashSet<_> = f1.modes.iter().collect();
            let m2: HashSet<_> = f2.modes.iter().collect();
            if m1 != m2 {
                return false;
            }
            let args1 = Record(
                f1.args
                    .iter()
                    .enumerate()
                    .map(|(i, ty)| Field {
                        id: Label::Id(i as u32),
                        ty: ty.clone(),
                    })
                    .collect(),
            );
            let args2 = Record(
                f2.args
                    .iter()
                    .enumerate()
                    .map(|(i, ty)| Field {
                        id: Label::Id(i as u32),
                        ty: ty.clone(),
                    })
                    .collect(),
            );
            let rets1 = Record(
                f1.rets
                    .iter()
                    .enumerate()
                    .map(|(i, ty)| Field {
                        id: Label::Id(i as u32),
                        ty: ty.clone(),
                    })
                    .collect(),
            );
            let rets2 = Record(
                f2.rets
                    .iter()
                    .enumerate()
                    .map(|(i, ty)| Field {
                        id: Label::Id(i as u32),
                        ty: ty.clone(),
                    })
                    .collect(),
            );
            subtype(env, &args2, &args1) && subtype(env, &rets1, &rets2)
        }
        (Class(_, _), Class(_, _)) => unreachable!(),
        (Unknown, _) => unreachable!(),
        (_, Unknown) => unreachable!(),
        (_, _) => false,
    }
}
