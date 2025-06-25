use anyhow::{bail, Result};
use candid_parser::candid::types::{
    subtype,
    syntax::{IDLType, IDLTypes},
    Type,
};
use candid_parser::{
    configs::Configs, parse_idl_args, parse_idl_type, parse_idl_value, pretty_check_file,
    pretty_parse_idl_types, pretty_wrap, typing::ast_to_type, Error, IDLArgs, IDLValue, TypeEnv,
};
use clap::Parser;
use console::style;
use std::collections::HashSet;
use std::io;
use std::path::PathBuf;
use std::str::FromStr;

#[derive(Parser)]
#[clap(version, author)]
enum Command {
    /// Type check Candid file
    Check {
        /// Specifies did file for type checking
        input: PathBuf,
        /// Specifies a previous version of did file for subtyping check
        previous: Option<PathBuf>,
        #[clap(short, long, requires("previous"))]
        /// Compare with structural equality, instead of subtyping
        strict: bool,
    },
    /// Generate binding for different languages
    Bind {
        /// Specifies did file for code generation
        input: PathBuf,
        #[clap(short, long, value_parser = ["js", "ts", "did", "mo", "rs", "rs-agent", "rs-stub"])]
        /// Specifies target language
        target: String,
        #[clap(short, long)]
        /// Specifies binding generation config in TOML syntax
        config: Option<String>,
        #[clap(short, long, num_args = 1.., value_delimiter = ',')]
        /// Specifies a subset of methods to generate bindings. Allowed format: "-m foo,bar", "-m foo bar", "-m foo -m bar"
        methods: Vec<String>,
    },
    /// Compute the hash of a field name
    Hash { input: String },
    /// Encode Candid value
    Encode {
        #[clap(value_parser = parse_args)]
        /// Specifies Candid textual format for encoding
        /// If omitted, the text will be read from stdin.
        args: Option<IDLArgs>,
        #[clap(flatten)]
        annotate: TypeAnnotation,
        #[clap(short, long, value_parser = ["hex", "pretty", "blob"], default_value = "hex")]
        /// Specifies hex format
        format: String,
    },
    /// Decode Candid binary data
    Decode {
        /// Specifies Candid binary data in hex string.
        /// If omitted, the hex will be read from stdin.
        blob: Option<String>,
        #[clap(short, long, value_parser = ["hex", "blob"], default_value = "hex")]
        /// Specifies hex format
        format: String,
        #[clap(flatten)]
        annotate: TypeAnnotation,
    },
    /// Generate textual Candid values based on a terminal dialog
    Assist {
        #[clap(flatten)]
        annotate: TypeAnnotation,
    },
    /// Generate random Candid values
    Random {
        #[clap(flatten)]
        annotate: TypeAnnotation,
        #[clap(short, long)]
        /// Specifies random value generation config in TOML syntax
        config: Option<String>,
        #[clap(short, long, value_parser = ["did", "js"], default_value = "did")]
        /// Specifies target language
        lang: String,
        #[clap(short, long, requires("method"))]
        #[clap(value_parser = parse_args)]
        /// Specifies input arguments for a method call, mocking the return result
        args: Option<IDLArgs>,
    },
    /// Check for subtyping
    Subtype {
        #[clap(short, long)]
        defs: Option<PathBuf>,
        #[clap(value_parser = parse_idl_type)]
        ty1: IDLType,
        #[clap(value_parser = parse_idl_type)]
        ty2: IDLType,
    },
}

#[derive(Parser)]
struct TypeAnnotation {
    #[clap(name = "types", short, long)]
    #[clap(value_parser = parse_types)]
    /// Annotates values with Candid types
    tys: Option<IDLTypes>,
    #[clap(short, long, conflicts_with("types"), requires("defs"))]
    /// Annotates values with a service method, specified in --defs option
    method: Option<String>,
    #[clap(short, long)]
    /// Loads did file for --types or --method to reference type definitions
    defs: Option<PathBuf>,
}

enum Mode {
    Encode,
    Decode,
}

impl TypeAnnotation {
    fn is_empty(&self) -> bool {
        self.tys.is_none() && self.method.is_none()
    }
    fn get_types(&self, mode: Mode) -> candid_parser::Result<(TypeEnv, Vec<Type>)> {
        let (env, actor) = if let Some(ref file) = self.defs {
            pretty_check_file(file)?
        } else {
            (TypeEnv::new(), None)
        };
        match (&self.tys, &self.method) {
            (None, None) => Err(Error::msg("no type annotations")),
            (Some(tys), None) => {
                let mut types = Vec::new();
                for ty in tys.args.iter() {
                    types.push(ast_to_type(&env, ty)?);
                }
                Ok((env, types))
            }
            (None, Some(meth)) => {
                let actor = actor
                    .ok_or_else(|| Error::msg("Cannot use --method with a non-service did file"))?;
                let func = env.get_method(&actor, meth)?;
                let types = match mode {
                    Mode::Encode => func.args.iter().map(|arg| arg.typ.clone()).collect(),
                    Mode::Decode => func.rets.clone(),
                };
                Ok((env, types))
            }
            _ => unreachable!(),
        }
    }
}

fn parse_args(str: &str) -> Result<IDLArgs, Error> {
    pretty_wrap("candid arguments", str, parse_idl_args)
}
fn parse_types(str: &str) -> Result<IDLTypes, Error> {
    pretty_parse_idl_types("type annotations", str)
}
fn load_config(input: &Option<String>) -> Result<Configs, Error> {
    match input {
        None => Configs::from_str(""),
        Some(str) if str.ends_with(".toml") => Configs::from_str(&std::fs::read_to_string(str)?),
        Some(str) => Configs::from_str(str),
    }
}
fn warn_unused(unused: &[String]) {
    for e in unused {
        eprintln!(
            "{} path {} is unused.",
            style("WARNING:").red().bold(),
            style(e).green(),
        );
    }
}

fn main() -> Result<()> {
    match Command::parse() {
        Command::Check {
            input,
            previous,
            strict,
        } => {
            let (mut env, opt_t1) = pretty_check_file(&input)?;
            if let Some(previous) = previous {
                let (env2, opt_t2) = pretty_check_file(&previous)?;
                match (opt_t1, opt_t2) {
                    (Some(t1), Some(t2)) => {
                        let mut gamma = HashSet::new();
                        let t2 = env.merge_type(env2, t2);
                        if strict {
                            subtype::equal(&mut gamma, &env, &t1, &t2)?;
                        } else {
                            subtype::subtype(&mut gamma, &env, &t1, &t2)?;
                        }
                    }
                    _ => {
                        bail!("did file need to contain the main service type for subtyping check")
                    }
                }
            }
        }
        Command::Subtype { defs, ty1, ty2 } => {
            let (env, _) = if let Some(file) = defs {
                pretty_check_file(&file)?
            } else {
                (TypeEnv::new(), None)
            };
            let ty1 = ast_to_type(&env, &ty1)?;
            let ty2 = ast_to_type(&env, &ty2)?;
            subtype::subtype(&mut HashSet::new(), &env, &ty1, &ty2)?;
        }
        Command::Bind {
            input,
            target,
            config,
            methods,
        } => {
            let configs = load_config(&config)?;
            let (env, mut actor) = pretty_check_file(&input)?;
            if !methods.is_empty() {
                actor = Some(candid_parser::bindings::analysis::project_methods(
                    &env, &actor, methods,
                )?);
            }
            let content = match target.as_str() {
                "js" => candid_parser::bindings::javascript::compile(&env, &actor),
                "ts" => candid_parser::bindings::typescript::compile(&env, &actor),
                "did" => candid_parser::pretty::candid::compile(&env, &actor),
                "mo" => candid_parser::bindings::motoko::compile(&env, &actor),
                "rs" => {
                    use candid_parser::bindings::rust::{compile, Config, ExternalConfig};
                    let external = configs
                        .get_subtable(&["didc".to_string(), "rust".to_string()])
                        .map(|x| x.clone().try_into().unwrap())
                        .unwrap_or(ExternalConfig::default());
                    let config = Config::new(configs);
                    let (res, unused) = compile(&config, &env, &actor, external);
                    warn_unused(&unused);
                    res
                }
                "rs-agent" | "rs-stub" => {
                    use candid_parser::bindings::rust::{compile, Config, ExternalConfig};
                    let config = Config::new(configs);
                    let mut external = ExternalConfig::default();
                    let target = match target.as_str() {
                        "rs-agent" => "agent",
                        "rs-stub" => "stub",
                        _ => unreachable!(),
                    };
                    external.0.insert("target".to_string(), target.to_string());
                    let (res, unused) = compile(&config, &env, &actor, external);
                    warn_unused(&unused);
                    res
                }
                _ => unreachable!(),
            };
            println!("{content}");
        }
        Command::Hash { input } => {
            println!("{}", candid_parser::idl_hash(&input));
        }
        Command::Assist { annotate } => {
            use candid_parser::assist::{input_args, Context};
            let (env, types) = annotate.get_types(Mode::Encode)?;
            let ctx = Context::new(env.clone());
            let args = input_args(&ctx, &types)?;
            println!("{args}");
            let bytes = args.to_bytes_with_types(&env, &types)?;
            println!("{}", hex::encode(bytes));
        }
        Command::Encode {
            args,
            format,
            annotate,
        } => {
            let args = match args {
                Some(idl_args) => idl_args,
                None => {
                    let text = io::read_to_string(io::stdin())?;
                    parse_args(&text)?
                }
            };
            let bytes = if annotate.is_empty() {
                args.to_bytes()?
            } else {
                let (env, types) = annotate.get_types(Mode::Encode)?;
                args.to_bytes_with_types(&env, &types)?
            };
            let hex = match format.as_str() {
                "hex" => hex::encode(&bytes),
                "pretty" => pretty_hex::pretty_hex(&bytes),
                "blob" => {
                    let mut res = String::new();
                    for ch in bytes.iter() {
                        res.push_str(&candid_parser::pretty::candid::value::pp_char(*ch));
                    }
                    format!("blob \"{res}\"")
                }
                _ => unreachable!(),
            };
            println!("{hex}");
        }
        Command::Decode {
            blob,
            format,
            annotate,
        } => {
            let blob = match blob {
                Some(blob) => blob,
                None => io::read_to_string(io::stdin())?,
            };
            let bytes = match format.as_str() {
                "hex" => hex::decode(
                    blob.chars()
                        .filter(|c| !c.is_whitespace())
                        .collect::<String>(),
                )?,
                "blob" => match pretty_wrap("blob", &blob, parse_idl_value)? {
                    IDLValue::Blob(blob) => blob,
                    _ => unreachable!(),
                },
                _ => unreachable!(),
            };
            let value = if annotate.is_empty() {
                IDLArgs::from_bytes(&bytes)?
            } else {
                let (env, types) = annotate.get_types(Mode::Decode)?;
                IDLArgs::from_bytes_with_types(&bytes, &env, &types)?
            };
            println!("{value}");
        }
        Command::Random {
            annotate,
            lang,
            config,
            args,
        } => {
            use candid_parser::configs::{Scope, ScopePos};
            use rand::Rng;
            let (env, types) = if args.is_some() {
                annotate.get_types(Mode::Decode)?
            } else {
                annotate.get_types(Mode::Encode)?
            };
            let config = load_config(&config)?;
            // TODO figure out how many bytes of entropy we need
            let seed: Vec<u8> = if let Some(ref args) = args {
                let (env, types) = annotate.get_types(Mode::Encode)?;
                let bytes = args.to_bytes_with_types(&env, &types)?;
                bytes.into_iter().rev().cycle().take(2048).collect()
            } else {
                let mut rng = rand::thread_rng();
                (0..2048).map(|_| rng.gen::<u8>()).collect()
            };
            let scope = annotate.method.as_ref().map(|method| {
                let position = Some(if args.is_some() {
                    ScopePos::Ret
                } else {
                    ScopePos::Arg
                });
                Scope { position, method }
            });
            let args = candid_parser::random::any(&seed, config, &env, &types, &scope)?;
            match lang.as_str() {
                "did" => println!("{args}"),
                "js" => println!(
                    "{}",
                    candid_parser::bindings::javascript::value::pp_args(&args).pretty(80)
                ),
                _ => unreachable!(),
            }
        }
    };
    Ok(())
}
