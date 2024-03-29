use crate::{check_prog, pretty_check_file, pretty_parse, Error, Result};
use candid::{types::Type, TypeEnv};
use std::path::Path;

pub enum CandidSource<'a> {
    File(&'a Path),
    Text(&'a str),
}

impl<'a> CandidSource<'a> {
    pub fn load(&self) -> Result<(TypeEnv, Option<Type>)> {
        Ok(match self {
            CandidSource::File(path) => pretty_check_file(path)?,
            CandidSource::Text(str) => {
                let ast = pretty_parse("", str)?;
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
    use candid::types::TypeInner;
    let (env, serv) = candid.load()?;
    let serv = serv.ok_or_else(|| Error::msg("the Candid interface has no main service type"))?;
    let serv = env.trace_type(&serv)?;
    Ok(match serv.as_ref() {
        TypeInner::Class(args, ty) => (args.clone(), (env, ty.clone())),
        TypeInner::Service(_) => (vec![], (env, serv)),
        _ => unreachable!(),
    })
}

/// Merge canister metadata candid:args and candid:service into a service constructor.
/// If candid:service already contains init args, returns the original did file.
pub fn merge_init_args(candid: &str, init: &str) -> Result<(TypeEnv, Type)> {
    use crate::{types::IDLInitArgs, typing::check_init_args};
    use candid::types::TypeInner;
    let candid = CandidSource::Text(candid);
    let (env, serv) = candid.load()?;
    let serv = serv.ok_or_else(|| Error::msg("the Candid interface has no main service type"))?;
    let serv = env.trace_type(&serv)?;
    match serv.as_ref() {
        TypeInner::Class(_, _) => Ok((env, serv)),
        TypeInner::Service(_) => {
            let prog = init.parse::<IDLInitArgs>()?;
            let mut env2 = TypeEnv::new();
            let args = check_init_args(&mut env2, &env, &prog)?;
            Ok((env2, TypeInner::Class(args, serv).into()))
        }
        _ => unreachable!(),
    }
}
