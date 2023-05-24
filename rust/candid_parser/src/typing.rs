use super::types::*;
use crate::{pretty_parse, Error, Result};
use candid::types::{Field, Function, Type, TypeEnv, TypeInner};
use std::collections::BTreeSet;
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
    check_type(&env, ast)
}

fn check_prim(prim: &PrimType) -> Type {
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
    .into()
}

pub fn check_type(env: &Env, t: &IDLType) -> Result<Type> {
    match t {
        IDLType::PrimT(prim) => Ok(check_prim(prim)),
        IDLType::VarT(id) => {
            env.te.find_type(id)?;
            Ok(TypeInner::Var(id.to_string()).into())
        }
        IDLType::OptT(t) => {
            let t = check_type(env, t)?;
            Ok(TypeInner::Opt(t).into())
        }
        IDLType::VecT(t) => {
            let t = check_type(env, t)?;
            Ok(TypeInner::Vec(t).into())
        }
        IDLType::RecordT(fs) => {
            let fs = check_fields(env, fs)?;
            Ok(TypeInner::Record(fs).into())
        }
        IDLType::VariantT(fs) => {
            let fs = check_fields(env, fs)?;
            Ok(TypeInner::Variant(fs).into())
        }
        IDLType::PrincipalT => Ok(TypeInner::Principal.into()),
        IDLType::FuncT(func) => {
            let mut t1 = Vec::new();
            for t in func.args.iter() {
                t1.push(check_type(env, t)?);
            }
            let mut t2 = Vec::new();
            for t in func.rets.iter() {
                t2.push(check_type(env, t)?);
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
            Ok(TypeInner::Func(f).into())
        }
        IDLType::ServT(ms) => {
            let ms = check_meths(env, ms)?;
            Ok(TypeInner::Service(ms).into())
        }
        IDLType::ClassT(_, _) => Err(Error::msg("service constructor not supported")),
    }
}

fn check_fields(env: &Env, fs: &[TypeField]) -> Result<Vec<Field>> {
    // field label duplication is checked in the parser
    let mut res = Vec::new();
    for f in fs.iter() {
        let ty = check_type(env, &f.typ)?;
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
        let t = check_type(env, &meth.typ)?;
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
            Dec::TypD(Binding { id, typ }) => {
                let t = check_type(env, typ)?;
                env.te.0.insert(id.to_string(), t);
            }
            Dec::ImportD(_) => (),
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
        if let Dec::TypD(Binding { id, typ: _ }) = dec {
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

fn combine_actors(env: &Env, actor1: &Option<Type>, actor2: &Option<Type>) -> Result<Option<Type>> {
    match (actor1, actor2) {
        (None, None) => Ok(None),
        (Some(t1), None) => Ok(Some(t1.clone())),
        (None, Some(t2)) => Ok(Some(t2.clone())),
        (Some(t1), Some(t2)) => {
            if let TypeInner::Class(_, _) = t1.as_ref() {
                return Err(Error::Custom(anyhow::Error::msg(format!(
                    "Cannot combine class type: {:?}",
                    t1
                ))));
            } else if let TypeInner::Class(_, _) = t2.as_ref() {
                return Err(Error::Custom(anyhow::Error::msg(format!(
                    "Cannot combine class type: {:?}",
                    t2
                ))));
            }

            let s1 = env.te.as_service(t1)?;
            let s2 = env.te.as_service(t2)?;
            // check that both actors don't have any overlapping names
            let names1 = s1.iter().map(|(n, _)| n).collect::<BTreeSet<_>>();
            let names2 = s2.iter().map(|(n, _)| n).collect::<BTreeSet<_>>();
            let intersection = names1.intersection(&names2).collect::<Vec<_>>();
            if !intersection.is_empty() {
                return Err(Error::Custom(anyhow::Error::msg(format!(
                    "duplicate method names: {:?} {:?} {:?}",
                    intersection, names1, names2
                ))));
            }

            let mut ret = s1.to_vec();
            ret.extend(s2.iter().cloned());

            Ok(Some(TypeInner::Service(ret).into()))
        }
    }
}

fn check_actor(env: &Env, actor: &Option<IDLType>) -> Result<Option<Type>> {
    match actor {
        None => Ok(None),
        Some(IDLType::ClassT(ts, t)) => {
            let mut args = Vec::new();
            for arg in ts.iter() {
                args.push(check_type(env, arg)?);
            }
            let serv = check_type(env, t)?;
            env.te.as_service(&serv)?;
            Ok(Some(TypeInner::Class(args, serv).into()))
        }
        Some(typ) => {
            let t = check_type(env, typ)?;
            env.te.as_service(&t)?;
            Ok(Some(t))
        }
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
    visited: &mut BTreeSet<PathBuf>,
    prog: &IDLProg,
    list: &mut Vec<(PathBuf, IDLProg)>,
) -> Result<()> {
    for dec in prog.decs.iter() {
        if let Dec::ImportD(file) = dec {
            let path = resolve_path(base, file);
            if visited.insert(path.clone()) {
                let code = std::fs::read_to_string(&path)
                    .map_err(|_| Error::msg(format!("Cannot import {file:?}")))?;
                let code = if is_pretty {
                    pretty_parse::<IDLProg>(path.to_str().unwrap(), &code)?
                } else {
                    code.parse::<IDLProg>()?
                };
                let base = path.parent().unwrap();
                load_imports(is_pretty, base, visited, &code, list)?;
                list.push((path, code));
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
) -> Result<Vec<Type>> {
    let mut env = Env { te, pre: false };
    check_decs(&mut env, &prog.decs)?;
    env.te.merge(main_env)?;
    let mut args = Vec::new();
    for arg in prog.args.iter() {
        args.push(check_type(&env, arg)?);
    }
    Ok(args)
}

fn check_file_(file: &Path, options: &CheckFileOptions) -> Result<CheckFileResult> {
    let is_pretty = options.pretty_errors;

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
    let mut imports = Vec::new();
    load_imports(is_pretty, &base, &mut BTreeSet::new(), &prog, &mut imports)?;
    let mut te = TypeEnv::new();
    let mut env = Env {
        te: &mut te,
        pre: false,
    };
    let mut actor: Option<Type> = None;
    for (_, import_prog) in imports.iter() {
        check_decs(&mut env, &import_prog.decs)?;
        if options.combine_actors {
            actor = combine_actors(&env, &actor, &check_actor(&env, &import_prog.actor)?)?;
        }
    }
    check_decs(&mut env, &prog.decs)?;
    let actor = if options.combine_actors {
        combine_actors(&env, &actor, &check_actor(&env, &prog.actor)?)?
    } else {
        check_actor(&env, &prog.actor)?
    };

    let types = te;

    Ok(CheckFileResult {
        types,
        actor,
        imports: imports.into_iter().map(|e| e.0).collect(),
    })
}

/// Type check did file including the imports.
pub fn check_file(file: &Path) -> Result<(TypeEnv, Option<Type>)> {
    let result = check_file_with_options(
        file,
        &CheckFileOptions {
            pretty_errors: false,
            ..Default::default()
        },
    )?;
    Ok((result.types, result.actor))
}

pub fn pretty_check_file(file: &Path) -> Result<(TypeEnv, Option<Type>)> {
    let result = check_file_with_options(
        file,
        &CheckFileOptions {
            pretty_errors: true,
            ..Default::default()
        },
    )?;
    Ok((result.types, result.actor))
}

/// Return type of `check_file_with_options`
#[derive(Debug, Default, Clone)]
pub struct CheckFileResult {
    pub types: TypeEnv,
    pub actor: Option<Type>,
    pub imports: BTreeSet<PathBuf>,
}

/// Options for `check_file_with_options`
#[derive(Debug, Default, Clone)]
pub struct CheckFileOptions {
    pub pretty_errors: bool,
    pub combine_actors: bool,
}

/// Type check did file including the imports. This variant
/// takes options to pretty check the file, and also combine
/// actors across imports into a single actor (useful for modular)
/// did files.
pub fn check_file_with_options(file: &Path, options: &CheckFileOptions) -> Result<CheckFileResult> {
    check_file_(file, options)
}
