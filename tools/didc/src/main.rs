use anyhow::Result;
use candid::parser::configs::Configs;
use candid::{
    check_prog, parser::types::IDLTypes, pretty_parse, types::Type, Error, IDLArgs, IDLProg,
    TypeEnv,
};
use ic_agent::export::Principal;
use std::path::{Path, PathBuf};
use structopt::clap::AppSettings;
use structopt::StructOpt;

#[derive(StructOpt)]
#[structopt(global_settings = &[AppSettings::ColoredHelp, AppSettings::DeriveDisplayOrder])]
enum Command {
    /// Type check Candid file
    Check {
        /// Specifies did file for type checking
        input: PathBuf,
    },
    /// Generate binding for different languages
    Bind {
        /// Specifies did file for code generation
        input: PathBuf,
        #[structopt(short, long, possible_values = &["js", "ts", "did"])]
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
        #[structopt(flatten)]
        annotate: TypeAnnotation,
        #[structopt(short, long)]
        /// Disable pretty printing
        flat: bool,
    },
    /// Generate random Candid values
    Random {
        #[structopt(flatten)]
        annotate: TypeAnnotation,
        #[structopt(flatten)]
        config: RandomConfig,
        #[structopt(short, long, possible_values = &["did", "js"], default_value = "did")]
        /// Specifies target language
        lang: String,
        #[structopt(short, long, requires("method"))]
        /// Specifies input arguments for a method call, mocking the return result
        args: Option<IDLArgs>,
    },
    /// Call canister method
    Call {
        canister_id: Principal,
        method: Option<String>,
        args: Option<IDLArgs>,
        #[structopt(short, long)]
        replica: Option<String>,
        #[structopt(flatten)]
        random: RandomConfig,
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

#[derive(StructOpt)]
struct RandomConfig {
    #[structopt(short, long, conflicts_with("file"))]
    /// Specifies random value generation config in Dhall syntax
    config: Option<String>,
    #[structopt(short, long)]
    /// Load random value generation config from file
    file: Option<String>,
    #[structopt(short, long)]
    /// Random seed
    seed: Option<Vec<u8>>,
}

impl RandomConfig {
    fn get_config(&self, method: &Option<String>) -> candid::Result<Configs> {
        let config = match (&self.config, &self.file) {
            (None, None) => Configs::from_dhall("{=}")?,
            (Some(str), None) => Configs::from_dhall(&str)?,
            (None, Some(file)) => {
                let content = std::fs::read_to_string(&file)
                    .map_err(|_| Error::msg(format!("could not read {}", file)))?;
                Configs::from_dhall(&content)?
            }
            _ => unreachable!(),
        };
        Ok(match method {
            None => config,
            Some(method) => config.with_method(method),
        })
    }
    fn get_seed(&self) -> Vec<u8> {
        use rand::Rng;
        if let Some(seed) = &self.seed {
            seed.to_vec()
        } else {
            let mut rng = rand::thread_rng();
            (0..4096).map(|_| rng.gen::<u8>()).collect()
        }
    }
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
        let mut env = TypeEnv::new();
        let actor = if let Some(ref file) = self.defs {
            check_file(&mut env, file)?
        } else {
            None
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
                let func = env.get_method(&actor, &meth)?;
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

fn check_file(env: &mut TypeEnv, file: &Path) -> candid::Result<Option<Type>> {
    let prog = std::fs::read_to_string(file)
        .map_err(|_| Error::msg(format!("could not read file {}", file.display())))?;
    let ast = pretty_parse::<IDLProg>(file.to_str().unwrap(), &prog)?;
    check_prog(env, &ast)
}

#[tokio::main]
async fn main() -> Result<()> {
    match Command::from_args() {
        Command::Check { input } => {
            let mut env = TypeEnv::new();
            check_file(&mut env, &input)?;
        }
        Command::Bind { input, target } => {
            let mut env = TypeEnv::new();
            let actor = check_file(&mut env, &input)?;
            let content = match target.as_str() {
                "js" => candid::bindings::javascript::compile(&env, &actor),
                "ts" => candid::bindings::typescript::compile(&env, &actor),
                "did" => candid::bindings::candid::compile(&env, &actor),
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
                    res
                }
                _ => unreachable!(),
            };
            println!("{}", hex);
        }
        Command::Decode {
            blob,
            annotate,
            flat,
        } => {
            let bytes = hex::decode(&blob)?;
            let value = if annotate.is_empty() {
                IDLArgs::from_bytes(&bytes)?
            } else {
                let (env, types) = annotate.get_types(Mode::Decode)?;
                IDLArgs::from_bytes_with_types(&bytes, &env, &types)?
            };
            if !flat {
                println!("{}", value);
            } else {
                println!("{:?}", value);
            }
        }
        Command::Random {
            annotate,
            lang,
            config,
            args,
        } => {
            let (env, types) = if args.is_some() {
                annotate.get_types(Mode::Decode)?
            } else {
                annotate.get_types(Mode::Encode)?
            };
            let seed = if let Some(ref args) = args {
                let (env, types) = annotate.get_types(Mode::Encode)?;
                let bytes = args.to_bytes_with_types(&env, &types)?;
                bytes.into_iter().rev().cycle().take(2048).collect()
            } else {
                config.get_seed()
            };
            let config = config.get_config(&annotate.method)?;
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
        Command::Call {
            replica,
            canister_id,
            method,
            args,
            random,
        } => {
            use candid::{Decode, Encode};
            use ic_agent::Agent;
            let replica = match replica.as_ref().map(|v| v.as_ref()) {
                None => "http://localhost:8000",
                Some("ic") => "https://gw.dfinity.network",
                Some(url) => url,
            };
            let agent = Agent::builder().with_url(replica).build()?;
            let response = agent
                .query(&canister_id, "__get_candid_interface_tmp_hack")
                .with_arg(&Encode!()?)
                .call()
                .await?;
            let response = Decode!(&response, &str)?;
            let ast = pretty_parse::<IDLProg>("fetched candid", response)?;
            let mut env = TypeEnv::new();
            let actor = check_prog(&mut env, &ast)?;
            match method {
                None => println!("{}", candid::bindings::candid::compile(&env, &actor)),
                Some(method) => {
                    let actor = actor.unwrap();
                    let func = env.get_method(&actor, &method)?;
                    let args = match args {
                        Some(args) => args,
                        None => {
                            let seed = random.get_seed();
                            let config = random.get_config(&Some(method.to_string()))?;
                            let args = IDLArgs::any(&seed, &config, &env, &func.args)?;
                            println!("Sending {}", args);
                            args
                        }
                    }
                    .to_bytes_with_types(&env, &func.args)?;
                    let bytes = if func.is_query() {
                        agent
                            .query(&canister_id, &method)
                            .with_arg(args)
                            .call()
                            .await?
                    } else {
                        agent.fetch_root_key().await?;
                        let waiter = delay::Delay::builder()
                            .exponential_backoff(std::time::Duration::from_secs(1), 1.1)
                            .timeout(std::time::Duration::from_secs(60 * 5))
                            .build();
                        agent
                            .update(&canister_id, &method)
                            .with_arg(args)
                            .call_and_wait(waiter)
                            .await?
                    };
                    let result = IDLArgs::from_bytes_with_types(&bytes, &env, &func.rets)?;
                    println!("{}", result);
                }
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
                let edit = candiff::value_diff(&v1, &v2, &None);
                println!("{}", candiff::pretty::value_edit(&edit).pretty(80));
            }
        }
    };
    Ok(())
}
