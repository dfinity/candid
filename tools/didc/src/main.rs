use candid::{check_prog, parser::types::IDLTypes, types::Type, IDLArgs, IDLProg, TypeEnv};
use exitfailure::ExitFailure;
use std::path::{Path, PathBuf};
use structopt::clap::AppSettings;
use structopt::StructOpt;

#[derive(StructOpt, Debug)]
#[structopt(global_settings = &[AppSettings::ColoredHelp, AppSettings::DeriveDisplayOrder])]
enum Command {
    #[structopt(about = "Type check Candid file")]
    Check { input: PathBuf },
    #[structopt(about = "Binding for different languages")]
    Bind {
        input: PathBuf,
        #[structopt(short, long, possible_values = &["js", "did"], case_insensitive = true)]
        format: String,
    },
    #[structopt(about = "Encode candid value")]
    Encode {
        args: IDLArgs,
        #[structopt(flatten)]
        annotate: TypeAnnotation,
        #[structopt(short, long)]
        pretty: bool,
    },
    #[structopt(about = "Decode candid binary data")]
    Decode {
        blob: String,
        #[structopt(flatten)]
        annotate: TypeAnnotation,
    },
}

#[derive(StructOpt, Debug)]
struct TypeAnnotation {
    #[structopt(name = "types", short, long)]
    tys: Option<IDLTypes>,
    #[structopt(short, long, requires("types"))]
    defs: Option<PathBuf>,
}

impl TypeAnnotation {
    fn annotate_types(&self, args: IDLArgs) -> candid::Result<IDLArgs> {
        match &self.tys {
            None => Ok(args),
            Some(tys) => {
                let mut env = TypeEnv::new();
                if let Some(ref file) = self.defs {
                    check_file(&mut env, file)?;
                }
                let mut res = Vec::new();
                for (v, ty) in args.args.iter().zip(tys.args.iter()) {
                    let ty = env.ast_to_type(ty)?;
                    let v = v.annotate_type(&env, &ty)?;
                    res.push(v);
                }
                Ok(IDLArgs { args: res })
            }
        }
    }
}

fn check_file(env: &mut TypeEnv, file: &Path) -> candid::Result<Option<Type>> {
    let prog = std::fs::read_to_string(file)
        .map_err(|_| candid::Error::msg(format!("could not read file {}", file.display())))?;
    let ast = prog.parse::<IDLProg>()?;
    check_prog(env, &ast)
}

fn main() -> Result<(), ExitFailure> {
    match Command::from_args() {
        Command::Check { input } => {
            let mut env = TypeEnv::new();
            check_file(&mut env, &input)?;
        }
        Command::Bind { input, format } => {
            let mut env = TypeEnv::new();
            let actor = check_file(&mut env, &input)?;
            let content = match format.as_str() {
                "js" => candid::bindings::javascript::compile(&env, &actor),
                "did" => candid::bindings::candid::compile(&env, &actor),
                _ => unreachable!(),
            };
            println!("{}", content);
        }
        Command::Encode {
            args,
            pretty,
            annotate,
        } => {
            let args = annotate.annotate_types(args)?;
            let bytes = args.to_bytes()?;
            let hex = if pretty {
                pretty_hex::pretty_hex(&bytes)
            } else {
                hex::encode(&bytes)
            };
            println!("{}", hex);
        }
        Command::Decode { blob, annotate } => {
            let bytes = hex::decode(&blob)?;
            let value = IDLArgs::from_bytes(&bytes)?;
            let value = annotate.annotate_types(value)?;
            println!("{}", value);
        }
    };
    Ok(())
}
