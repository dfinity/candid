use crate::{
    check_prog, pretty_check_file, pretty_parse_idl_prog, typing::ast_to_type, Error, Result,
};
use candid::{
    types::{
        syntax::{Binding, IDLEnv, IDLType},
        Type, TypeInner,
    },
    TypeEnv,
};
use std::path::Path;

pub enum CandidSource<'a> {
    File(&'a Path),
    Text(&'a str),
}

impl CandidSource<'_> {
    pub fn load(&self) -> Result<(TypeEnv, IDLEnv, Option<IDLType>)> {
        Ok(match self {
            CandidSource::File(path) => pretty_check_file(path)?,
            CandidSource::Text(str) => {
                let ast = pretty_parse_idl_prog("", str)?;
                let mut env = TypeEnv::new();
                let idl_env = IDLEnv::from(&ast);
                let actor = check_prog(&mut env, &ast)?;
                (env, idl_env, actor)
            }
        })
    }
}

/// Check compatibility of two service types
pub fn service_compatible(new: CandidSource, old: CandidSource) -> Result<()> {
    let (mut env, _, t1) = new.load()?;
    let t1 = t1
        .ok_or_else(|| Error::msg("new interface has no main service type"))
        .and_then(|t| ast_to_type(&env, &t))?;
    let (env2, _, t2) = old.load()?;
    let t2 = t2
        .ok_or_else(|| Error::msg("old interface has no main service type"))
        .and_then(|t| ast_to_type(&env, &t))?;
    let mut gamma = std::collections::HashSet::new();
    let t2 = env.merge_type(env2, t2);
    candid::types::subtype::subtype(&mut gamma, &env, &t1, &t2)?;
    Ok(())
}

/// Check structural equality of two service types
pub fn service_equal(left: CandidSource, right: CandidSource) -> Result<()> {
    let (mut env, _, t1) = left.load()?;
    let t1 = t1
        .ok_or_else(|| Error::msg("left interface has no main service type"))
        .and_then(|t| ast_to_type(&env, &t))?;
    let (env2, _, t2) = right.load()?;
    let t2 = t2
        .ok_or_else(|| Error::msg("right interface has no main service type"))
        .and_then(|t| ast_to_type(&env, &t))?;
    let mut gamma = std::collections::HashSet::new();
    let t2 = env.merge_type(env2, t2);
    candid::types::subtype::equal(&mut gamma, &env, &t1, &t2)?;
    Ok(())
}

/// Take a did file and outputs the init args and the service type (without init args).
/// If the original did file contains imports, the output flattens the type definitions.
/// For now, the comments from the original did file is omitted.
pub fn instantiate_candid(candid: CandidSource) -> Result<(Vec<Type>, (TypeEnv, Type))> {
    let (env, _, serv) = candid.load()?;
    let serv = serv
        .ok_or_else(|| Error::msg("the Candid interface has no main service type"))
        .and_then(|t| ast_to_type(&env, &t))?;
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
pub fn get_metadata(env: &IDLEnv) -> Option<String> {
    let serv = env.actor.clone()?;
    let serv = env.trace_type(&serv).ok()?;
    let serv = match &serv {
        IDLType::ClassT(_, ty) => ty.as_ref(),
        IDLType::ServT(_) => &serv,
        _ => unreachable!(),
    };
    let def_list = crate::bindings::analysis::chase_actor(env, serv).ok()?;
    let mut filtered = IDLEnv::new();
    for d in def_list {
        if let Ok((id, typ)) = env.find_binding(d) {
            filtered.insert_binding(Binding {
                id: id.to_string(),
                typ: typ.clone(),
            });
        }
    }
    filtered.set_actor(Some(serv.clone()));
    Some(candid::pretty::candid::compile(&filtered))
}

/// Merge canister metadata candid:args and candid:service into a service constructor.
/// If candid:service already contains init args, returns the original did file.
pub fn merge_init_args(candid: &str, init: &str) -> Result<(TypeEnv, Type)> {
    use crate::{parse_idl_init_args, typing::check_init_args};
    use candid::types::TypeInner;
    let candid = CandidSource::Text(candid);
    let (env, mut idl_env, serv) = candid.load()?;
    let serv = serv
        .ok_or_else(|| Error::msg("the Candid interface has no main service type"))
        .and_then(|t| ast_to_type(&env, &t))?;
    let serv = env.trace_type(&serv)?;
    match serv.as_ref() {
        TypeInner::Class(_, _) => Ok((env, serv)),
        TypeInner::Service(_) => {
            let prog = parse_idl_init_args(init)?;
            let mut env2 = TypeEnv::new();
            let args = check_init_args(&mut env2, &env, &mut idl_env, &prog)?;
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
    let mut idl_env = IDLEnv::new();
    let args = check_init_args(&mut env, &TypeEnv::new(), &mut idl_env, &parsed)?;
    let mut rust_env = TypeContainer::new();
    let ty = rust_env.add::<T>();
    let ty = env.merge_type(rust_env.idl_env.into(), ty.into());
    let mut gamma = std::collections::HashSet::new();
    equal(&mut gamma, &env, &args[0].typ, &ty)?;
    Ok(())
}
