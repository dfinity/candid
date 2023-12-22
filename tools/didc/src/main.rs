use anyhow::{bail, Result};
use candid_parser::candid::types::{subtype, Type};
use candid_parser::{
    error::pretty_diagnose,
    parse_idl_args, parse_idl_value, pretty_check_file, pretty_parse,
    types::{IDLType, IDLTypes},
    typing::ast_to_type,
    Error, IDLArgs, IDLValue, TypeEnv,
};
use clap::Parser;
use std::collections::HashSet;
use std::io;
use std::path::PathBuf;

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
        #[clap(short, long, value_parser = ["js", "ts", "did", "mo", "rs", "rs-agent"])]
        /// Specifies target language
        target: String,
    },
    /// Generate test suites for different languages
    Test {
        /// Specifies .test.did file for test suites generation
        input: PathBuf,
        #[clap(short, long, value_parser = ["js", "did"], default_value = "js")]
        /// Specifies target language
        target: String,
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
        #[clap(short, long, conflicts_with("file"))]
        /// Specifies random value generation config in Dhall syntax
        config: Option<String>,
        #[clap(short, long)]
        /// Load random value generation config from file
        file: Option<String>,
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
        ty1: IDLType,
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
                    Mode::Encode => &func.args,
                    Mode::Decode => &func.rets,
                }
                .clone();
                Ok((env, types))
            }
            _ => unreachable!(),
        }
    }
}

fn parse_args(str: &str) -> Result<IDLArgs, Error> {
    parse_idl_args(str).map_err(|e| {
        let _ = pretty_diagnose("candid arguments", str, &e);
        e
    })
}
fn parse_types(str: &str) -> Result<IDLTypes, Error> {
    pretty_parse("type annotations", str)
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
        Command::Bind { input, target } => {
            let (env, actor) = pretty_check_file(&input)?;
            let content = match target.as_str() {
                "js" => candid_parser::bindings::javascript::compile(&env, &actor),
                "ts" => candid_parser::bindings::typescript::compile(&env, &actor),
                "did" => candid_parser::pretty::candid::compile(&env, &actor),
                "mo" => candid_parser::bindings::motoko::compile(&env, &actor),
                "rs" => {
                    let config = candid_parser::bindings::rust::Config::new();
                    candid_parser::bindings::rust::compile(&config, &env, &actor)
                }
                "rs-agent" => {
                    let mut config = candid_parser::bindings::rust::Config::new();
                    config.set_target(candid_parser::bindings::rust::Target::Agent);
                    candid_parser::bindings::rust::compile(&config, &env, &actor)
                }
                _ => unreachable!(),
            };
            println!("{content}");
        }
        Command::Test { input, target } => {
            let test = std::fs::read_to_string(&input)
                .map_err(|_| Error::msg(format!("could not read file {}", input.display())))?;
            let ast = pretty_parse::<candid_parser::test::Test>(input.to_str().unwrap(), &test)?;
            let content = match target.as_str() {
                "js" => candid_parser::bindings::javascript::test::test_generate(ast),
                "did" => {
                    candid_parser::test::check(ast)?;
                    "".to_string()
                }
                _ => unreachable!(),
            };
            println!("{content}");
        }
        Command::Hash { input } => {
            println!("{}", candid_parser::idl_hash(&input));
        }
        Command::Assist { annotate } => {
            let (env, types) = annotate.get_types(Mode::Encode)?;
            let args = candid_parser::assist::input_args(&env, &types)?;
            println!("{args}");
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
                "blob" => {
                    match parse_idl_value(&blob).map_err(|e| {
                        let _ = pretty_diagnose("blob", &blob, &e);
                        e
                    })? {
                        IDLValue::Blob(blob) => blob,
                        _ => unreachable!(),
                    }
                }
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
            file,
            args,
        } => {
            use candid_parser::configs::Configs;
            use rand::Rng;
            let (env, types) = if args.is_some() {
                annotate.get_types(Mode::Decode)?
            } else {
                annotate.get_types(Mode::Encode)?
            };
            let config = match (config, file) {
                (None, None) => Configs::from_dhall("{=}")?,
                (Some(str), None) => Configs::from_dhall(&str)?,
                (None, Some(file)) => {
                    let content = std::fs::read_to_string(&file)
                        .map_err(|_| Error::msg(format!("could not read {file}")))?;
                    Configs::from_dhall(&content)?
                }
                _ => unreachable!(),
            };
            let config = if let Some(ref method) = annotate.method {
                config.with_method(method)
            } else {
                config
            };
            // TODO figure out how many bytes of entropy we need
            let seed: Vec<u8> = if let Some(ref args) = args {
                let (env, types) = annotate.get_types(Mode::Encode)?;
                let bytes = args.to_bytes_with_types(&env, &types)?;
                bytes.into_iter().rev().cycle().take(2048).collect()
            } else {
                let mut rng = rand::thread_rng();
                (0..2048).map(|_| rng.gen::<u8>()).collect()
            };
            let args = candid_parser::random::any(&seed, &config, &env, &types)?;
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
