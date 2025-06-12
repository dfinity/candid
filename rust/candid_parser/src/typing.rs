use super::types::*;
use crate::{pretty_parse, Error, Result};
use candid::types::{ArgType, Field, Function, Type, TypeEnv, TypeInner};
use candid::utils::check_unique;
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

pub struct Env<'a> {
    pub te: &'a mut TypeEnv,
    pub pre: bool,
}

/// Convert candid AST to internal Type
pub fn ast_to_type(env: &TypeEnv, ast: &super::types::IDLType) -> Result<Type> {
    let env = Env {
        te: &mut env.clone(),
        pre: false,
    };
    check_type(&env, ast, None)
}

fn check_prim(prim: &PrimType) -> TypeInner {
    match prim {
        PrimType::Nat => TypeInner::Nat,
        PrimType::Nat8 => TypeInner::Nat8,
        PrimType::Nat16 => TypeInner::Nat16,
        PrimType::Nat32 => TypeInner::Nat32,
        PrimType::Nat64 => TypeInner::Nat64,
        PrimType::Int => TypeInner::Int,
        PrimType::Int8 => TypeInner::Int8,
        PrimType::Int16 => TypeInner::Int16,
        PrimType::Int32 => TypeInner::Int32,
        PrimType::Int64 => TypeInner::Int64,
        PrimType::Float32 => TypeInner::Float32,
        PrimType::Float64 => TypeInner::Float64,
        PrimType::Bool => TypeInner::Bool,
        PrimType::Text => TypeInner::Text,
        PrimType::Null => TypeInner::Null,
        PrimType::Reserved => TypeInner::Reserved,
        PrimType::Empty => TypeInner::Empty,
    }
}

pub fn check_type(env: &Env, t: &IDLType, comment: Option<&String>) -> Result<Type> {
    let inner = match t {
        IDLType::PrimT(prim) => Ok(check_prim(prim)),
        IDLType::VarT(id) => {
            env.te.find_type(id)?;
            Ok(TypeInner::Var(id.to_string()))
        }
        IDLType::OptT(t) => {
            let t = check_type(env, t, comment)?;
            Ok(TypeInner::Opt(t))
        }
        IDLType::VecT(t) => {
            let t = check_type(env, t, comment)?;
            Ok(TypeInner::Vec(t))
        }
        IDLType::RecordT(fs) => {
            let fs = check_fields(env, fs)?;
            Ok(TypeInner::Record(fs))
        }
        IDLType::VariantT(fs) => {
            let fs = check_fields(env, fs)?;
            Ok(TypeInner::Variant(fs))
        }
        IDLType::PrincipalT => Ok(TypeInner::Principal),
        IDLType::FuncT(func) => {
            let mut t1 = Vec::new();
            for arg in func.args.iter() {
                t1.push(check_arg(env, arg)?);
            }
            let mut t2 = Vec::new();
            for t in func.rets.iter() {
                t2.push(check_type(env, t, comment)?);
            }
            if func.modes.len() > 1 {
                return Err(Error::msg("cannot have more than one mode"));
            }
            if func.modes.len() == 1
                && func.modes[0] == candid::types::FuncMode::Oneway
                && !t2.is_empty()
            {
                return Err(Error::msg("oneway function has non-unit return type"));
            }
            let f = Function {
                modes: func.modes.clone(),
                args: t1,
                rets: t2,
            };
            Ok(TypeInner::Func(f))
        }
        IDLType::ServT(ms) => {
            let ms = check_meths(env, ms)?;
            Ok(TypeInner::Service(ms))
        }
        IDLType::ClassT(_, _) => Err(Error::msg("service constructor not supported")),
    }?;
    Ok((inner, comment).into())
}

fn check_arg(env: &Env, arg: &IDLArgType) -> Result<ArgType> {
    Ok(ArgType {
        name: arg.name.clone(),
        typ: check_type(env, &arg.typ, None)?, // args don't have comments
    })
}

fn check_fields(env: &Env, fs: &[TypeField]) -> Result<Vec<Field>> {
    // field label duplication is checked in the parser
    let mut res = Vec::new();
    for f in fs.iter() {
        let ty = check_type(env, &f.typ, f.comment.as_ref().map(|c| &c.text))?;
        let field = Field {
            id: f.label.clone().into(),
            ty,
        };
        res.push(field);
    }
    Ok(res)
}

fn check_meths(env: &Env, ms: &[Binding]) -> Result<Vec<(String, Type)>> {
    // binding duplication is checked in the parser
    let mut res = Vec::new();
    for meth in ms.iter() {
        let t = check_type(env, &meth.typ, meth.comment.as_ref().map(|c| &c.text))?;
        if !env.pre && env.te.as_func(&t).is_err() {
            return Err(Error::msg(format!(
                "method {} is a non-function type",
                meth.id
            )));
        }
        res.push((meth.id.to_owned(), t));
    }
    Ok(res)
}

fn check_defs(env: &mut Env, decs: &[Dec]) -> Result<()> {
    for dec in decs.iter() {
        match dec {
            Dec::TypD(Binding { id, typ, comment }) => {
                let t = check_type(env, typ, comment.as_ref().map(|c| &c.text))?;
                env.te.0.insert(id.to_string(), t);
            }
            Dec::ImportType(_) | Dec::ImportServ(_) => (),
        }
    }
    Ok(())
}

fn check_cycle(env: &TypeEnv) -> Result<()> {
    fn has_cycle<'a>(seen: &mut BTreeSet<&'a str>, env: &'a TypeEnv, t: &'a Type) -> Result<bool> {
        match t.as_ref() {
            TypeInner::Var(id) => {
                if seen.insert(id) {
                    let ty = env.find_type(id)?;
                    has_cycle(seen, env, ty)
                } else {
                    Ok(true)
                }
            }
            _ => Ok(false),
        }
    }
    for (id, ty) in env.0.iter() {
        let mut seen = BTreeSet::new();
        if has_cycle(&mut seen, env, ty)? {
            return Err(Error::msg(format!("{id} has cyclic type definition")));
        }
    }
    Ok(())
}

fn check_decs(env: &mut Env, decs: &[Dec]) -> Result<()> {
    for dec in decs.iter() {
        if let Dec::TypD(Binding { id, .. }) = dec {
            let duplicate = env.te.0.insert(id.to_string(), TypeInner::Unknown.into());
            if duplicate.is_some() {
                return Err(Error::msg(format!("duplicate binding for {id}")));
            }
        }
    }
    env.pre = true;
    check_defs(env, decs)?;
    check_cycle(env.te)?;
    env.pre = false;
    check_defs(env, decs)?;
    Ok(())
}

fn check_actor(env: &Env, actor: &Option<ActorBinding>) -> Result<Option<Type>> {
    if let Some(ActorBinding { typ, comment }) = actor {
        let comment = comment.as_ref().map(|c| c.text.clone());
        match typ {
            IDLType::ClassT(ts, t) => {
                let mut args = Vec::new();
                for arg in ts.iter() {
                    args.push(check_arg(env, arg)?);
                }
                let serv = check_type(env, t, None)?;
                env.te.as_service(&serv)?;
                Ok(Some(
                    (TypeInner::Class(args, serv), comment.as_ref()).into(),
                ))
            }
            _ => {
                let t = check_type(env, typ, comment.as_ref())?;
                env.te.as_service(&t)?;
                Ok(Some(t))
            }
        }
    } else {
        Ok(None)
    }
}

fn resolve_path(base: &Path, file: &str) -> PathBuf {
    // TODO use shellexpand to support tilde
    let file = PathBuf::from(file);
    if file.is_absolute() {
        file
    } else {
        base.join(file)
    }
}

fn load_imports(
    is_pretty: bool,
    base: &Path,
    visited: &mut BTreeMap<PathBuf, bool>,
    prog: &IDLProg,
    list: &mut Vec<(PathBuf, String)>,
) -> Result<()> {
    for dec in prog.decs.iter() {
        let include_serv = matches!(dec, Dec::ImportServ(_));
        if let Dec::ImportType(file) | Dec::ImportServ(file) = dec {
            let path = resolve_path(base, file);
            match visited.get_mut(&path) {
                Some(x) => *x = *x || include_serv,
                None => {
                    visited.insert(path.clone(), include_serv);
                    let code = std::fs::read_to_string(&path)
                        .map_err(|_| Error::msg(format!("Cannot import {file:?}")))?;
                    let code = if is_pretty {
                        pretty_parse::<IDLProg>(path.to_str().unwrap(), &code)?
                    } else {
                        code.parse::<IDLProg>()?
                    };
                    let base = path.parent().unwrap();
                    load_imports(is_pretty, base, visited, &code, list)?;
                    list.push((path, file.to_string()));
                }
            }
        }
    }
    Ok(())
}

/// Type check IDLProg and adds bindings to type environment. Returns
/// the main actor if present. This function ignores the imports.
pub fn check_prog(te: &mut TypeEnv, prog: &IDLProg) -> Result<Option<Type>> {
    let mut env = Env { te, pre: false };
    check_decs(&mut env, &prog.decs)?;
    check_actor(&env, &prog.actor)
}
/// Type check init args extracted from canister metadata candid:args.
/// Need to provide `main_env`, because init args may refer to variables from the main did file.
pub fn check_init_args(
    te: &mut TypeEnv,
    main_env: &TypeEnv,
    prog: &IDLInitArgs,
) -> Result<Vec<ArgType>> {
    let mut env = Env { te, pre: false };
    check_decs(&mut env, &prog.decs)?;
    env.te.merge(main_env)?;
    let mut args = Vec::new();
    for arg in prog.args.iter() {
        args.push(check_arg(&env, arg)?);
    }
    Ok(args)
}

fn merge_actor(
    env: &Env,
    actor: &Option<Type>,
    imported: &Option<Type>,
    file: &str,
) -> Result<Option<Type>> {
    match imported {
        None => Err(Error::msg(format!(
            "Imported service file {file:?} has no main service"
        ))),
        Some(t) => {
            let t = env.te.trace_type(t)?;
            match t.as_ref() {
                TypeInner::Class(_, _) => Err(Error::msg(format!(
                    "Imported service file {file:?} has a service constructor"
                ))),
                TypeInner::Service(meths) => match actor {
                    None => Ok(Some(t)),
                    Some(t) => {
                        let t = env.te.trace_type(t)?;
                        let serv = env.te.as_service(&t)?;
                        let mut ms: Vec<_> = serv.iter().chain(meths.iter()).cloned().collect();
                        ms.sort_unstable_by(|a, b| a.0.partial_cmp(&b.0).unwrap());
                        check_unique(ms.iter().map(|m| &m.0)).map_err(|e| {
                            Error::msg(format!("Duplicate imported method name: {e}"))
                        })?;
                        let res: Type = TypeInner::Service(ms).into();
                        Ok(Some(res))
                    }
                },
                _ => unreachable!(),
            }
        }
    }
}

fn check_file_(file: &Path, is_pretty: bool) -> Result<(TypeEnv, Option<Type>)> {
    let base = if file.is_absolute() {
        file.parent().unwrap().to_path_buf()
    } else {
        std::env::current_dir()?
            .join(file)
            .parent()
            .unwrap()
            .to_path_buf()
    };
    let prog =
        std::fs::read_to_string(file).map_err(|_| Error::msg(format!("Cannot open {file:?}")))?;
    let prog = if is_pretty {
        pretty_parse::<IDLProg>(file.to_str().unwrap(), &prog)?
    } else {
        prog.parse::<IDLProg>()?
    };
    let mut visited = BTreeMap::new();
    let mut imports = Vec::new();
    load_imports(is_pretty, &base, &mut visited, &prog, &mut imports)?;
    let imports: Vec<_> = imports
        .iter()
        .map(|file| match visited.get(&file.0) {
            Some(x) => (*x, &file.0, &file.1),
            None => unreachable!(),
        })
        .collect();
    let mut te = TypeEnv::new();
    let mut env = Env {
        te: &mut te,
        pre: false,
    };
    let mut actor: Option<Type> = None;
    for (include_serv, path, name) in imports.iter() {
        let code = std::fs::read_to_string(path)?;
        let code = code.parse::<IDLProg>()?;
        check_decs(&mut env, &code.decs)?;
        if *include_serv {
            let t = check_actor(&env, &code.actor)?;
            actor = merge_actor(&env, &actor, &t, name)?;
        }
    }
    check_decs(&mut env, &prog.decs)?;
    let mut res = check_actor(&env, &prog.actor)?;
    if actor.is_some() {
        res = merge_actor(&env, &res, &actor, "")?;
    }
    Ok((te, res))
}

/// Type check did file including the imports.
pub fn check_file(file: &Path) -> Result<(TypeEnv, Option<Type>)> {
    check_file_(file, false)
}
pub fn pretty_check_file(file: &Path) -> Result<(TypeEnv, Option<Type>)> {
    check_file_(file, true)
}
