use crate::{parse_idl_prog, pretty_parse_idl_prog, Error, Result};
use candid::types::{
    syntax::{
        Binding, Dec, IDLArgType, IDLInitArgs, IDLMergedProg, IDLProg, IDLType, PrimType, TypeField,
    },
    ArgType, Field, Function, Type, TypeEnv, TypeInner,
};
use candid::utils::check_unique;
use std::collections::{BTreeMap, HashMap};
use std::path::{Path, PathBuf};

pub struct Env<'a> {
    pub te: &'a mut TypeEnv,
    doc_comments_in_actor: HashMap<String, Vec<String>>,
    can_insert_doc_comments: bool,
    pub pre: bool,
}

impl<'a> Env<'a> {
    fn new_with_te(te: &'a mut TypeEnv) -> Self {
        Self {
            te,
            doc_comments_in_actor: HashMap::new(),
            can_insert_doc_comments: false,
            pre: false,
        }
    }

    /// Insert doc comments if [Env::can_insert_doc_comments] is true and there is a doc comment.
    fn insert_comments_if_allowed(&mut self, id: &str, doc_comment: Option<&Vec<String>>) {
        if !self.can_insert_doc_comments {
            return;
        }

        if let Some(doc_comment) = doc_comment {
            self.doc_comments_in_actor
                .insert(id.to_string(), doc_comment.to_vec());
        }
    }
}

/// Convert candid AST to internal Type
pub fn ast_to_type(env: &TypeEnv, ast: &IDLType) -> Result<Type> {
    let mut te = env.clone();
    let mut env = Env::new_with_te(&mut te);
    check_type(&mut env, ast)
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

pub fn check_type(env: &mut Env, t: &IDLType) -> Result<Type> {
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
        IDLType::FutureT => Err(Error::msg("future not supported")),
        IDLType::UnknownT => Err(Error::msg("unknown type not supported")),
    }
}

fn check_arg(env: &mut Env, arg: &IDLArgType) -> Result<ArgType> {
    Ok(ArgType {
        name: arg.name.clone(),
        typ: check_type(env, &arg.typ)?,
    })
}

fn check_fields(env: &mut Env, fs: &[TypeField]) -> Result<Vec<Field>> {
    // field label duplication is checked in the parser
    let mut res = Vec::new();
    for f in fs.iter() {
        let ty = check_type(env, &f.typ)?;
        let field = Field {
            id: f.label.clone().into(),
            ty,
        };
        res.push(field);
        env.insert_comments_if_allowed(&f.label.to_string(), f.doc_comment.as_ref());
    }
    Ok(res)
}

fn check_meths(env: &mut Env, ms: &[Binding]) -> Result<Vec<(String, Type)>> {
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
        env.insert_comments_if_allowed(&meth.id, meth.doc_comment.as_ref());
    }
    Ok(res)
}

fn check_defs(env: &mut Env, decs: &[Dec]) -> Result<()> {
    for dec in decs.iter() {
        match dec {
            Dec::TypD(Binding {
                id,
                typ,
                doc_comment: _,
            }) => {
                let t = check_type(env, typ)?;
                env.te.0.insert(id.to_string(), t);
            }
            Dec::ImportType(_) | Dec::ImportServ(_) => (),
        }
    }
    Ok(())
}

fn check_decs(env: &mut Env, decs: &[Dec]) -> Result<()> {
    for dec in decs.iter() {
        if let Dec::TypD(Binding {
            id,
            typ: _,
            doc_comment: _,
        }) = dec
        {
            let duplicate = env.te.0.insert(id.to_string(), TypeInner::Unknown.into());
            if duplicate.is_some() {
                return Err(Error::msg(format!("duplicate binding for {id}")));
            }
        }
    }
    env.pre = true;
    check_defs(env, decs)?;
    env.te.check_cycle()?;
    env.pre = false;
    check_defs(env, decs)?;
    Ok(())
}

fn check_actor(env: &mut Env, actor: &Option<IDLType>) -> Result<Option<Type>> {
    env.can_insert_doc_comments = true;
    let res = match actor {
        None => Ok(None),
        Some(IDLType::ClassT(ts, t)) => {
            let mut args = Vec::new();
            for arg in ts.iter() {
                args.push(check_arg(env, arg)?);
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
    };
    env.can_insert_doc_comments = false;
    res
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
pub fn check_prog(te: &mut TypeEnv, prog: &IDLProg) -> Result<Option<Type>> {
    let mut env = Env::new_with_te(te);
    check_decs(&mut env, &prog.decs)?;
    check_actor(&mut env, &prog.actor)
}
/// Type check init args extracted from canister metadata candid:args.
/// Need to provide `main_env`, because init args may refer to variables from the main did file.
pub fn check_init_args(
    te: &mut TypeEnv,
    main_env: &TypeEnv,
    prog: &IDLInitArgs,
) -> Result<Vec<ArgType>> {
    let mut env = Env::new_with_te(te);
    check_decs(&mut env, &prog.decs)?;
    env.te.merge(main_env)?;
    let mut args = Vec::new();
    for arg in prog.args.iter() {
        args.push(check_arg(&mut env, arg)?);
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
    let mut env = Env::new_with_te(&mut te);
    let mut idl_merged_prog = IDLMergedProg::new();

    let mut actor: Option<Type> = None;
    for (include_serv, path, name) in imports.iter() {
        let code = std::fs::read_to_string(path)?;
        let code = parse_idl_prog(&code)?;
        check_decs(&mut env, &code.decs)?;
        idl_merged_prog.add_decs(&code.decs);
        if *include_serv {
            let t = check_actor(&mut env, &code.actor)?;
            actor = merge_actor(&env, &actor, &t, name)?;
        }
    }

    check_decs(&mut env, &prog.decs)?;
    idl_merged_prog.add_decs(&prog.decs);

    let mut res = check_actor(&mut env, &prog.actor)?;
    if actor.is_some() {
        res = merge_actor(&env, &res, &actor, "")?;
    }

    idl_merged_prog.set_actor(res.clone().map(|t| env.te.as_idl_type(&t)));
    idl_merged_prog.set_comments_in_actor(&env.doc_comments_in_actor);

    Ok((te, res, idl_merged_prog))
}

/// Type check did file including the imports.
pub fn check_file(file: &Path) -> Result<(TypeEnv, Option<Type>, IDLMergedProg)> {
    check_file_(file, false)
}
pub fn pretty_check_file(file: &Path) -> Result<(TypeEnv, Option<Type>, IDLMergedProg)> {
    check_file_(file, true)
}
