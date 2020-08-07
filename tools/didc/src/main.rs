use candid::{check_prog, parser::types::IDLType, types::Type, IDLArgs, IDLProg, TypeEnv};
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
    #[structopt(name = "type", short, long)]
    ty: Option<IDLType>,
    #[structopt(short, long, requires("type"))]
    defs: Option<PathBuf>,
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
        Command::Encode { args, pretty, .. } => {
            let bytes = args.to_bytes()?;
            let hex = if pretty {
                pretty_hex::pretty_hex(&bytes)
            } else {
                hex::encode(&bytes)
            };
            println!("{}", hex);
        }
        Command::Decode { blob, .. } => {
            let bytes = hex::decode(&blob)?;
            let value = IDLArgs::from_bytes(&bytes)?;
            println!("{}", value);
        }
    };
    Ok(())
}
