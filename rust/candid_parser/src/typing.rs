use crate::{
    pretty_parse,
    syntax::{
        Binding, Dec, IDLActorType, IDLInitArgs, IDLMergedProg, IDLProg, IDLType, PrimType,
        TypeField,
    },
    Error, Result,
};
use candid::types::{Field, Function, Type, TypeEnv, TypeInner};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

pub struct Env<'a> {
    pub te: &'a mut TypeEnv,
    pub pre: bool,
}

/// Convert candid AST to internal Type
pub fn ast_to_type(env: &TypeEnv, ast: &IDLType) -> Result<Type> {
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
            for arg in func.args.iter() {
                t1.push(check_type(env, &arg.typ)?);
            }
            let mut t2 = Vec::new();
            for t in func.rets.iter() {
                t2.push(check_type(env, &t.typ)?);
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
            Dec::TypD(Binding { id, typ, docs: _ }) => {
                let t = check_type(env, typ)?;
                env.te.0.insert(id.to_string(), t);
            }
            Dec::ImportType(_) | Dec::ImportServ(_) => (),
        }
    }
    Ok(())
}

/// Reject a chain of aliases that leads back to itself with no type
/// constructor in between (`type a = b; type b = a`).
///
/// Each name is walked once: a chain that reaches a name already known to be
/// acyclic stops there. Restarting from every name would be quadratic on long
/// alias chains, and the walk is a loop, not a recursion, so its stack use
/// does not grow with the chain either.
fn check_cycle(env: &TypeEnv) -> Result<()> {
    let mut acyclic: BTreeSet<&str> = BTreeSet::new();
    for (id, ty) in env.0.iter() {
        let mut path: BTreeSet<&str> = BTreeSet::new();
        path.insert(id.as_str());
        let mut t = ty;
        while let TypeInner::Var(next) = t.as_ref() {
            if acyclic.contains(next.as_str()) {
                break;
            }
            if !path.insert(next.as_str()) {
                return Err(Error::msg(format!("{id} has cyclic type definition")));
            }
            t = env.find_type(next)?;
        }
        acyclic.extend(path);
    }
    Ok(())
}

/// Check that every type reachable from the definitions is well formed (so
/// far: every method of a service has a function type).
///
/// It visits each named type once and uses an explicit worklist rather than
/// recursion, so a long chain of aliases cannot overflow the stack.
fn validate_decs(env: &TypeEnv) -> Result<()> {
    let mut seen: BTreeSet<&str> = BTreeSet::new();
    let mut todo: Vec<&Type> = env.0.values().collect();
    while let Some(t) = todo.pop() {
        match t.as_ref() {
            TypeInner::Null
            | TypeInner::Bool
            | TypeInner::Nat
            | TypeInner::Int
            | TypeInner::Nat8
            | TypeInner::Nat16
            | TypeInner::Nat32
            | TypeInner::Nat64
            | TypeInner::Int8
            | TypeInner::Int16
            | TypeInner::Int32
            | TypeInner::Int64
            | TypeInner::Float32
            | TypeInner::Float64
            | TypeInner::Text
            | TypeInner::Reserved
            | TypeInner::Empty
            | TypeInner::Unknown
            | TypeInner::Principal
            | TypeInner::Future
            | TypeInner::Knot(_) => (),
            TypeInner::Var(id) => {
                if seen.insert(id.as_str()) {
                    todo.push(env.find_type(id)?);
                }
            }
            TypeInner::Opt(ty) | TypeInner::Vec(ty) => todo.push(ty),
            TypeInner::Record(fields) | TypeInner::Variant(fields) => {
                todo.extend(fields.iter().map(|f| &f.ty));
            }
            TypeInner::Func(func) => todo.extend(func.args.iter().chain(func.rets.iter())),
            TypeInner::Service(methods) => {
                for (_, ty) in methods.iter() {
                    let func = env.as_func(ty)?;
                    todo.extend(func.args.iter().chain(func.rets.iter()));
                }
            }
            TypeInner::Class(args, ty) => {
                todo.extend(args.iter());
                todo.push(ty);
            }
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
    validate_decs(env.te)?;
    Ok(())
}

fn check_actor(env: &Env, actor: &Option<IDLActorType>) -> Result<Option<Type>> {
    match actor.as_ref().map(|a| &a.typ) {
        None => Ok(None),
        Some(IDLType::ClassT(ts, t)) => {
            let mut args = Vec::new();
            for arg in ts.iter() {
                args.push(check_type(env, &arg.typ)?);
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
    visited: &mut BTreeMap<PathBuf, bool>,
    prog: &IDLProg,
    list: &mut Vec<(PathBuf, String, IDLProg)>,
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
                    let prog = if is_pretty {
                        pretty_parse::<IDLProg>(path.to_str().unwrap(), &code)?
                    } else {
                        code.parse::<IDLProg>()?
                    };
                    let base = path.parent().unwrap();
                    load_imports(is_pretty, base, visited, &prog, list)?;
                    list.push((path, file.to_string(), prog));
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
) -> Result<Vec<Type>> {
    let mut env = Env { te, pre: false };
    check_decs(&mut env, &prog.decs)?;
    env.te.merge(main_env)?;
    let mut args = Vec::new();
    for arg in prog.args.iter() {
        args.push(check_type(&env, &arg.typ)?);
    }
    Ok(args)
}

fn check_file_(file: &Path, is_pretty: bool) -> Result<(TypeEnv, Option<Type>, IDLMergedProg)> {
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

    let mut merged_prog: IDLMergedProg = IDLMergedProg::new(prog);
    for (path, name, prog) in imports {
        let include_service = visited.get(&path).unwrap();
        merged_prog.merge(*include_service, name, prog)?;
    }

    let mut te = TypeEnv::new();
    let mut env = Env {
        te: &mut te,
        pre: false,
    };
    check_decs(&mut env, &merged_prog.decs())?;
    let res = check_actor(&env, &merged_prog.resolve_actor()?)?;
    Ok((te, res, merged_prog))
}

/// Type check did file including the imports.
pub fn check_file(file: &Path) -> Result<(TypeEnv, Option<Type>, IDLMergedProg)> {
    check_file_(file, false)
}
pub fn pretty_check_file(file: &Path) -> Result<(TypeEnv, Option<Type>, IDLMergedProg)> {
    check_file_(file, true)
}
