use crate::{parse_idl_prog, pretty_parse_idl_prog, Error, Result};
use candid::types::{
    syntax::{
        Binding, Dec, FuncType, IDLArgType, IDLEnv, IDLInitArgs, IDLProg, IDLType, PrimType,
        TypeField,
    },
    ArgType, Field, Function, Type, TypeEnv, TypeInner,
};
use candid::utils::check_unique;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

pub struct Env<'a> {
    te: &'a mut TypeEnv,
    idl_env: &'a mut IDLEnv,
    pre: bool,
}

impl Env<'_> {
    fn insert_type(&mut self, id: String, t: Type, binding: IDLType) {
        self.te.0.insert(id.clone(), t);
        self.idl_env.insert_binding(Binding { id, typ: binding });
    }

    fn visit_id(&mut self, id: String) -> Result<()> {
        let duplicate = self.te.0.insert(id.clone(), TypeInner::Unknown.into());
        if duplicate.is_some() {
            return Err(Error::msg(format!("duplicate binding for {id}")));
        }
        self.idl_env.insert_unknown(id);
        Ok(())
    }
}

/// Convert candid AST to internal Type
pub fn ast_to_type(env: &TypeEnv, ast: &IDLType) -> Result<Type> {
    let env = Env {
        te: &mut env.clone(),
        idl_env: &mut IDLEnv::new(),
        pre: false,
    };
    map_type(&env, ast)
}

fn map_prim(prim: &PrimType) -> Type {
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

pub fn map_type(env: &Env, t: &IDLType) -> Result<Type> {
    match t {
        IDLType::PrimT(prim) => Ok(map_prim(prim)),
        IDLType::VarT(id) => {
            env.te.find_type(id)?;
            Ok(TypeInner::Var(id.to_string()).into())
        }
        IDLType::OptT(t) => {
            let t = map_type(env, t)?;
            Ok(TypeInner::Opt(t).into())
        }
        IDLType::VecT(t) => {
            let t = map_type(env, t)?;
            Ok(TypeInner::Vec(t).into())
        }
        IDLType::RecordT(fs) => {
            let fs = map_fields(env, fs)?;
            Ok(TypeInner::Record(fs).into())
        }
        IDLType::VariantT(fs) => {
            let fs = map_fields(env, fs)?;
            Ok(TypeInner::Variant(fs).into())
        }
        IDLType::PrincipalT => Ok(TypeInner::Principal.into()),
        IDLType::FuncT(func) => {
            let mut t1 = Vec::new();
            for arg in func.args.iter() {
                t1.push(map_arg(env, arg)?);
            }
            let mut t2 = Vec::new();
            for t in func.rets.iter() {
                t2.push(map_type(env, t)?);
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
            let ms = map_meths(env, ms)?;
            Ok(TypeInner::Service(ms).into())
        }
        IDLType::KnotT(id) => Ok(TypeInner::Knot(id.clone()).into()),
        IDLType::ClassT(_, _) => Err(Error::msg("service constructor not supported")),
    }
}

fn map_arg(env: &Env, arg: &IDLArgType) -> Result<ArgType> {
    Ok(ArgType {
        name: arg.name.clone(),
        typ: map_type(env, &arg.typ)?,
    })
}

fn map_fields(env: &Env, fs: &[TypeField]) -> Result<Vec<Field>> {
    // field label duplication is checked in the parser
    let mut res = Vec::new();
    for f in fs.iter() {
        let ty = map_type(env, &f.typ)?;
        let field = Field {
            id: f.label.clone().into(),
            ty,
        };
        res.push(field);
    }
    Ok(res)
}

fn map_meths(env: &Env, ms: &[Binding]) -> Result<Vec<(String, Type)>> {
    // binding duplication is checked in the parser
    let mut res = Vec::new();
    for meth in ms.iter() {
        let t = map_type(env, &meth.typ)?;
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

pub fn check_type(env: &Env, t: &IDLType) -> Result<IDLType> {
    match t {
        IDLType::PrimT(prim) => Ok(IDLType::PrimT(prim.clone())),
        IDLType::VarT(id) => {
            env.idl_env.assert_has_type(id).map_err(Error::msg)?;
            Ok(IDLType::VarT(id.to_string()))
        }
        IDLType::OptT(t) => {
            let t = check_type(env, t)?;
            Ok(IDLType::OptT(Box::new(t)))
        }
        IDLType::VecT(t) => {
            let t = check_type(env, t)?;
            Ok(IDLType::VecT(Box::new(t)))
        }
        IDLType::RecordT(fs) => {
            let fs = check_fields(env, fs)?;
            Ok(IDLType::RecordT(fs))
        }
        IDLType::VariantT(fs) => {
            let fs = check_fields(env, fs)?;
            Ok(IDLType::VariantT(fs))
        }
        IDLType::PrincipalT => Ok(IDLType::PrincipalT),
        IDLType::FuncT(func) => {
            let mut t1 = Vec::new();
            for arg in func.args.iter() {
                t1.push(check_arg(env, arg)?);
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
            let f = FuncType {
                modes: func.modes.clone(),
                args: t1,
                rets: t2,
            };
            Ok(IDLType::FuncT(f))
        }
        IDLType::ServT(ms) => {
            let ms = check_meths(env, ms)?;
            Ok(IDLType::ServT(ms))
        }
        IDLType::ClassT(_, _) => Err(Error::msg("service constructor not supported")),
        IDLType::KnotT(_) => Err(Error::msg("knot type not supported")),
    }
}

fn check_arg(env: &Env, arg: &IDLArgType) -> Result<IDLArgType> {
    Ok(IDLArgType {
        name: arg.name.clone(),
        typ: check_type(env, &arg.typ).map_err(Error::msg)?,
    })
}

fn check_fields(env: &Env, fs: &[TypeField]) -> Result<Vec<TypeField>> {
    // field label duplication is checked in the parser
    let mut res = Vec::new();
    for f in fs.iter() {
        let typ = check_type(env, &f.typ).map_err(Error::msg)?;
        let field = TypeField {
            label: f.label.clone(),
            typ,
        };
        res.push(field);
    }
    Ok(res)
}

fn check_meths(env: &Env, ms: &[Binding]) -> Result<Vec<Binding>> {
    // binding duplication is checked in the parser
    let mut res = Vec::new();
    for meth in ms.iter() {
        let t = check_type(env, &meth.typ)?;
        if !env.pre && env.idl_env.as_func(&t).is_err() {
            return Err(Error::msg(format!(
                "method {} is a non-function type",
                meth.id
            )));
        }
        res.push(Binding {
            id: meth.id.to_owned(),
            typ: t,
        });
    }
    Ok(res)
}

fn check_defs(env: &mut Env, decs: &[Dec]) -> Result<()> {
    for dec in decs.iter() {
        match dec {
            Dec::TypD(Binding { id, typ }) => {
                let idl_type = check_type(env, typ)?;
                let t = map_type(env, &idl_type)?;
                env.insert_type(id.to_string(), t, idl_type);
            }
            Dec::ImportType(_) | Dec::ImportServ(_) => (),
        }
    }
    Ok(())
}

fn check_decs(env: &mut Env, decs: &[Dec]) -> Result<()> {
    for dec in decs.iter() {
        if let Dec::TypD(Binding { id, typ: _ }) = dec {
            env.visit_id(id.to_string())?;
        }
    }
    env.pre = true;
    check_defs(env, decs)?;
    env.te.check_cycle()?;
    env.pre = false;
    check_defs(env, decs)?;
    Ok(())
}

fn check_actor(env: &Env, actor: &Option<IDLType>) -> Result<Option<IDLType>> {
    match actor {
        None => Ok(None),
        Some(typ) => {
            let serv = if let IDLType::ClassT(ts, t) = typ {
                let mut args = Vec::new();
                for arg in ts.iter() {
                    args.push(check_arg(env, arg)?);
                }
                let t = check_type(env, t)?;
                env.idl_env.as_service(&t).map_err(Error::msg)?;
                IDLType::ClassT(args, Box::new(t))
            } else {
                let serv = check_type(env, typ)?;
                env.idl_env.as_service(&serv).map_err(Error::msg)?;
                serv
            };
            Ok(Some(serv))
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
                        pretty_parse_idl_prog(path.to_str().unwrap(), &code)?
                    } else {
                        parse_idl_prog(&code)?
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
pub fn check_prog(te: &mut TypeEnv, prog: &IDLProg) -> Result<Option<IDLType>> {
    let mut env = Env {
        te,
        idl_env: &mut IDLEnv::new(),
        pre: false,
    };
    check_decs(&mut env, &prog.decs)?;
    check_actor(&env, &prog.actor)
}
/// Type check init args extracted from canister metadata candid:args.
/// Need to provide `main_env`, because init args may refer to variables from the main did file.
pub fn check_init_args(
    te: &mut TypeEnv,
    main_env: &TypeEnv,
    idl_env: &mut IDLEnv,
    prog: &IDLInitArgs,
) -> Result<Vec<ArgType>> {
    let mut env = Env {
        te,
        idl_env,
        pre: false,
    };
    check_decs(&mut env, &prog.decs)?;
    env.te.merge(main_env)?;
    let mut args = Vec::new();
    for arg in prog.args.iter() {
        args.push(check_arg(&env, arg).and_then(|t| {
            Ok(ArgType {
                name: t.name,
                typ: ast_to_type(env.te, &t.typ)?,
            })
        })?);
    }
    Ok(args)
}

fn merge_actor(
    env: &Env,
    actor: &Option<IDLType>,
    imported: &Option<IDLType>,
    file: &str,
) -> Result<Option<IDLType>> {
    match imported {
        None => Err(Error::msg(format!(
            "Imported service file {file:?} has no main service"
        ))),
        Some(idl_type) => {
            let t = env.idl_env.trace_type(idl_type).map_err(Error::msg)?;
            match &t {
                IDLType::ClassT(_, _) => Err(Error::msg(format!(
                    "Imported service file {file:?} has a service constructor"
                ))),
                IDLType::ServT(meths) => match &actor {
                    None => Ok(Some(t)),
                    Some(idl_type) => {
                        let t = env.idl_env.trace_type(idl_type).map_err(Error::msg)?;
                        let serv = env.idl_env.as_service(&t).map_err(Error::msg)?;
                        let mut ms: Vec<_> = serv.iter().chain(meths.iter()).cloned().collect();
                        ms.sort_unstable_by(|a, b| a.id.partial_cmp(&b.id).unwrap());
                        check_unique(ms.iter().map(|m| &m.id)).map_err(|e| {
                            Error::msg(format!("Duplicate imported method name: {e}"))
                        })?;
                        let res = IDLType::ServT(ms);
                        Ok(Some(res))
                    }
                },
                _ => unreachable!(),
            }
        }
    }
}

fn check_file_(file: &Path, is_pretty: bool) -> Result<(TypeEnv, IDLEnv, Option<IDLType>)> {
    let base = if file.is_absolute() {
        file.parent().unwrap().to_path_buf()
    } else {
        std::env::current_dir()?
            .join(file)
            .parent()
            .unwrap()
            .to_path_buf()
    };

    let prog = {
        let prog = std::fs::read_to_string(file)
            .map_err(|_| Error::msg(format!("Cannot open {file:?}")))?;
        if is_pretty {
            pretty_parse_idl_prog(file.to_str().unwrap(), &prog)?
        } else {
            parse_idl_prog(&prog)?
        }
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
    let mut idl_env = IDLEnv::new();
    let mut env = Env {
        te: &mut te,
        idl_env: &mut idl_env,
        pre: false,
    };

    let mut actor: Option<IDLType> = None;
    for (include_serv, path, name) in imports.iter() {
        let code = std::fs::read_to_string(path)?;
        let code = parse_idl_prog(&code)?;
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
    idl_env.set_actor(res.clone());

    Ok((te, idl_env, res))
}

/// Type check did file including the imports.
pub fn check_file(file: &Path) -> Result<(TypeEnv, IDLEnv, Option<IDLType>)> {
    check_file_(file, false)
}
pub fn pretty_check_file(file: &Path) -> Result<(TypeEnv, IDLEnv, Option<IDLType>)> {
    check_file_(file, true)
}
