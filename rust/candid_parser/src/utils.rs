use crate::{check_prog, pretty_check_file, pretty_parse_idl_prog, Error, Result};
use candid::{
    types::{Type, TypeInner},
    TypeEnv,
};
use std::path::Path;

pub enum CandidSource<'a> {
    File(&'a Path),
    Text(&'a str),
}

impl CandidSource<'_> {
    pub fn load(&self) -> Result<(TypeEnv, Option<Type>)> {
        Ok(match self {
            CandidSource::File(path) => pretty_check_file(path)?,
            CandidSource::Text(str) => {
                let ast = pretty_parse_idl_prog("", str)?;
                let mut env = TypeEnv::new();
                let actor = check_prog(&mut env, &ast)?;
                (env, actor)
            }
        })
    }
}

/// Check compatibility of two service types
pub fn service_compatible(new: CandidSource, old: CandidSource) -> Result<()> {
    let (mut env, t1) = new.load()?;
    let t1 = t1.ok_or_else(|| Error::msg("new interface has no main service type"))?;
    let (env2, t2) = old.load()?;
    let t2 = t2.ok_or_else(|| Error::msg("old interface has no main service type"))?;
    let mut gamma = std::collections::HashSet::new();
    let t2 = env.merge_type(env2, t2);
    candid::types::subtype::subtype(&mut gamma, &env, &t1, &t2)?;
    Ok(())
}

/// Check structural equality of two service types
pub fn service_equal(left: CandidSource, right: CandidSource) -> Result<()> {
    let (mut env, t1) = left.load()?;
    let t1 = t1.ok_or_else(|| Error::msg("left interface has no main service type"))?;
    let (env2, t2) = right.load()?;
    let t2 = t2.ok_or_else(|| Error::msg("right interface has no main service type"))?;
    let mut gamma = std::collections::HashSet::new();
    let t2 = env.merge_type(env2, t2);
    candid::types::subtype::equal(&mut gamma, &env, &t1, &t2)?;
    Ok(())
}

/// Take a did file and outputs the init args and the service type (without init args).
/// If the original did file contains imports, the output flattens the type definitions.
/// For now, the comments from the original did file is omitted.
pub fn instantiate_candid(candid: CandidSource) -> Result<(Vec<Type>, (TypeEnv, Type))> {
    let (env, serv) = candid.load()?;
    let serv = serv.ok_or_else(|| Error::msg("the Candid interface has no main service type"))?;
    let serv = env.trace_type(&serv)?;
    Ok(match serv.as_ref() {
        TypeInner::Class(args, ty) => (
            args.iter().map(|arg| arg.typ.clone()).collect::<Vec<_>>(),
            (env, ty.clone()),
        ),
        TypeInner::Service(_) => (vec![], (env, serv)),
        _ => unreachable!(),
    })
}
pub fn get_metadata(env: &TypeEnv, serv: &Option<Type>) -> Option<String> {
    let serv = serv.clone()?;
    let serv = env.trace_type(&serv).ok()?;
    let serv = match serv.as_ref() {
        TypeInner::Class(_, ty) => ty.clone(),
        TypeInner::Service(_) => serv,
        _ => unreachable!(),
    };
    let def_list = crate::bindings::analysis::chase_actor(env, &serv).ok()?;
    let mut filtered = TypeEnv::new();
    for d in def_list {
        if let Some(t) = env.0.get(d) {
            filtered.0.insert(d.to_string(), t.clone());
        }
    }
    Some(candid::pretty::candid::compile(&filtered, &Some(serv)))
}

/// Merge canister metadata candid:args and candid:service into a service constructor.
/// If candid:service already contains init args, returns the original did file.
pub fn merge_init_args(candid: &str, init: &str) -> Result<(TypeEnv, Type)> {
    use crate::{parse_idl_init_args, typing::check_init_args};
    use candid::types::TypeInner;
    let candid = CandidSource::Text(candid);
    let (env, serv) = candid.load()?;
    let serv = serv.ok_or_else(|| Error::msg("the Candid interface has no main service type"))?;
    let serv = env.trace_type(&serv)?;
    match serv.as_ref() {
        TypeInner::Class(_, _) => Ok((env, serv)),
        TypeInner::Service(_) => {
            let prog = parse_idl_init_args(init)?;
            let mut env2 = TypeEnv::new();
            let args = check_init_args(&mut env2, &env, &prog)?;
            Ok((env2, TypeInner::Class(args, serv).into()))
        }
        _ => unreachable!(),
    }
}
/// Check if a Rust type implements a Candid type. The candid type is given using the init args format.
/// Note that this only checks structural equality, not equivalence. For recursive types, it may reject
/// an unrolled type.
pub fn check_rust_type<T: candid::CandidType>(candid_args: &str) -> Result<()> {
    use crate::{parse_idl_init_args, typing::check_init_args};
    use candid::types::{internal::TypeContainer, subtype::equal, TypeEnv};
    let parsed = parse_idl_init_args(candid_args)?;
    let mut env = TypeEnv::new();
    let args = check_init_args(&mut env, &TypeEnv::new(), &parsed)?;
    let mut rust_env = TypeContainer::new();
    let ty = rust_env.add::<T>();
    let ty = env.merge_type(rust_env.env, ty);
    let mut gamma = std::collections::HashSet::new();
    equal(&mut gamma, &env, &args[0].typ, &ty)?;
    Ok(())
}
