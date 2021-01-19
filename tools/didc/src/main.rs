use anyhow::Result;
use candid::{
    check_prog, parser::types::IDLTypes, pretty_parse, types::Type, Error, IDLArgs, IDLProg,
    TypeEnv,
};
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
        #[structopt(short, long, possible_values = &["js", "did"])]
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

fn main() -> Result<()> {
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
                        res.push_str(&candid::parser::value::pretty::pp_char(*ch));
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
