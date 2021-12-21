use anyhow::{bail, Result};
use candid::{
    parser::types::{IDLType, IDLTypes},
    pretty_check_file, pretty_parse,
    types::Type,
    Error, IDLArgs, TypeEnv,
};
use std::collections::HashSet;
use std::path::PathBuf;
use structopt::clap::AppSettings;
use structopt::StructOpt;

#[derive(StructOpt)]
#[structopt(global_settings = &[AppSettings::ColoredHelp, AppSettings::DeriveDisplayOrder])]
enum Command {
    /// Type check Candid file
    Check {
        /// Specifies did file for type checking
        input: PathBuf,
        /// Specifies a previous version of did file for subtyping check
        previous: Option<PathBuf>,
    },
    /// Generate binding for different languages
    Bind {
        /// Specifies did file for code generation
        input: PathBuf,
        #[structopt(short, long, possible_values = &["js", "ts", "did", "mo", "rs"])]
        /// Specifies target language
        target: String,
    },
    /// Generate test suites for different languages
    Test {
        /// Specifies .test.did file for test suites generation
        input: PathBuf,
        #[structopt(short, long, possible_values = &["js", "did"], default_value = "js")]
        /// Specifies target language
        target: String,
    },
    /// Compute the hash of a field name
    Hash { input: String },
    /// Encode Candid value
    Encode {
        #[structopt(parse(try_from_str = parse_args))]
        /// Specifies Candid textual format for encoding
        args: IDLArgs,
        #[structopt(flatten)]
        annotate: TypeAnnotation,
        #[structopt(short, long, possible_values = &["hex", "pretty", "blob"], default_value = "hex")]
        /// Specifies hex format
        format: String,
    },
    /// Decode Candid binary data
    Decode {
        /// Specifies Candid binary data in hex string
        blob: String,
        #[structopt(short, long, possible_values = &["hex", "blob"], default_value = "hex")]
        /// Specifies hex format
        format: String,
        #[structopt(flatten)]
        annotate: TypeAnnotation,
    },
    /// Generate random Candid values
    Random {
        #[structopt(flatten)]
        annotate: TypeAnnotation,
        #[structopt(short, long, conflicts_with("file"))]
        /// Specifies random value generation config in Dhall syntax
        config: Option<String>,
        #[structopt(short, long)]
        /// Load random value generation config from file
        file: Option<String>,
        #[structopt(short, long, possible_values = &["did", "js"], default_value = "did")]
        /// Specifies target language
        lang: String,
        #[structopt(short, long, requires("method"))]
        /// Specifies input arguments for a method call, mocking the return result
        args: Option<IDLArgs>,
    },
    /// Check for subtyping
    Subtype {
        #[structopt(short, long)]
        defs: Option<PathBuf>,
        ty1: IDLType,
        ty2: IDLType,
    },
    /// Diff two Candid values
    Diff {
        #[structopt(parse(try_from_str = parse_args))]
        values1: IDLArgs,
        #[structopt(parse(try_from_str = parse_args))]
        values2: IDLArgs,
        #[structopt(flatten)]
        annotate: TypeAnnotation,
    },
}

#[derive(StructOpt)]
struct TypeAnnotation {
    #[structopt(name = "types", short, long)]
    #[structopt(parse(try_from_str = parse_types))]
    /// Annotates values with Candid types
    tys: Option<IDLTypes>,
    #[structopt(short, long, conflicts_with("types"), requires("defs"))]
    /// Annotates values with a service method, specified in --defs option
    method: Option<String>,
    #[structopt(short, long)]
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
    fn get_types(&self, mode: Mode) -> candid::Result<(TypeEnv, Vec<Type>)> {
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
                    types.push(env.ast_to_type(ty)?);
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
    pretty_parse("candid arguments", str)
}
fn parse_types(str: &str) -> Result<IDLTypes, Error> {
    pretty_parse("type annotations", str)
}

fn main() -> Result<()> {
    match Command::from_args() {
        Command::Check { input, previous } => {
            let (mut env, opt_t1) = pretty_check_file(&input)?;
            if let Some(previous) = previous {
                let (env2, opt_t2) = pretty_check_file(&previous)?;
                match (opt_t1, opt_t2) {
                    (Some(t1), Some(t2)) => {
                        let mut gamma = HashSet::new();
                        let t2 = env.merge_type(env2, t2);
                        candid::types::subtype::subtype(&mut gamma, &env, &t1, &t2)?;
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
            let ty1 = env.ast_to_type(&ty1)?;
            let ty2 = env.ast_to_type(&ty2)?;
            candid::types::subtype::subtype(&mut HashSet::new(), &env, &ty1, &ty2)?;
        }
        Command::Bind { input, target } => {
            let (env, actor) = pretty_check_file(&input)?;
            let content = match target.as_str() {
                "js" => candid::bindings::javascript::compile(&env, &actor),
                "ts" => candid::bindings::typescript::compile(&env, &actor),
                "did" => candid::bindings::candid::compile(&env, &actor),
                "mo" => candid::bindings::motoko::compile(&env, &actor),
                "rs" => candid::bindings::rust::compile(&env, &actor),
                _ => unreachable!(),
            };
            println!("{}", content);
        }
        Command::Test { input, target } => {
            let test = std::fs::read_to_string(&input)
                .map_err(|_| Error::msg(format!("could not read file {}", input.display())))?;
            let ast = pretty_parse::<candid::parser::test::Test>(input.to_str().unwrap(), &test)?;
            let content = match target.as_str() {
                "js" => candid::bindings::javascript::test::test_generate(ast),
                "did" => {
                    candid::parser::test::check(ast)?;
                    "".to_string()
                }
                _ => unreachable!(),
            };
            println!("{}", content);
        }
        Command::Hash { input } => {
            println!("{}", candid::idl_hash(&input));
        }
        Command::Encode {
            args,
            format,
            annotate,
        } => {
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
                        res.push_str(&candid::parser::pretty::pp_char(*ch));
                    }
                    format!("blob \"{}\"", res)
                }
                _ => unreachable!(),
            };
            println!("{}", hex);
        }
        Command::Decode {
            blob,
            format,
            annotate,
        } => {
            let bytes = match format.as_str() {
                "hex" => hex::decode(&blob)?,
                "blob" => {
                    use candid::parser::value::IDLValue;
                    match pretty_parse::<IDLValue>("blob", &blob)? {
                        IDLValue::Vec(vec) => vec
                            .iter()
                            .map(|v| {
                                if let IDLValue::Nat8(u) = v {
                                    *u
                                } else {
                                    unreachable!()
                                }
                            })
                            .collect(),
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
            println!("{}", value);
        }
        Command::Random {
            annotate,
            lang,
            config,
            file,
            args,
        } => {
            use candid::parser::configs::Configs;
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
                        .map_err(|_| Error::msg(format!("could not read {}", file)))?;
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
            let args = IDLArgs::any(&seed, &config, &env, &types)?;
            match lang.as_str() {
                "did" => println!("{}", args),
                "js" => println!(
                    "{}",
                    candid::bindings::javascript::value::pp_args(&args).pretty(80)
                ),
                _ => unreachable!(),
            }
        }
        Command::Diff {
            values1,
            values2,
            annotate,
        } => {
            let (vs1, vs2) = if annotate.is_empty() {
                (values1.args, values2.args)
            } else {
                // Either we assume the types are in decode mode, or forbid the use of --method in diff
                let (env, types) = annotate.get_types(Mode::Decode)?;
                (
                    values1.annotate_types(true, &env, &types)?.args,
                    values2.annotate_types(true, &env, &types)?.args,
                )
            };
            if vs1.len() != vs2.len() {
                return Err(Error::msg("value length mismatch").into());
            }
            for (v1, v2) in vs1.iter().zip(vs2.iter()) {
                let edit = candiff::value_diff(v1, v2, &None);
                println!("{}", candiff::pretty::value_edit(&edit).pretty(80));
            }
        }
    };
    Ok(())
}
