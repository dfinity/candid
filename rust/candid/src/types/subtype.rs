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
            fs2.iter()
                .all(|Field { id, ty: ty2 }| match fields.get(id) {
                    Some(ty1) => subtype(env, ty1, ty2),
                    None => subtype(env, &Opt(Box::new(Empty)), ty2),
                })
        }
        (Variant(fs1), Variant(fs2)) => {
            let fields: HashMap<_, _> = fs2.iter().map(|Field { id, ty }| (id, ty)).collect();
            fs1.iter()
                .all(|Field { id, ty: ty1 }| match fields.get(id) {
                    Some(ty2) => subtype(env, ty1, ty2),
                    None => false,
                })
        }
        (Service(ms1), Service(ms2)) => {
            let meths: HashMap<_, _> = ms2.iter().map(|(name, ty)| (name, ty)).collect();
            ms1.iter().all(|(name, ty1)| match meths.get(name) {
                Some(ty2) => subtype(env, ty1, ty2),
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
            subtype(env, &args2, &args1) && subtype(env, &rets1, &rets2)
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
