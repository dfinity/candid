extern crate clap;
use clap::Shell;
use std::str::FromStr;

// Logging:
#[macro_use]
extern crate log;
extern crate env_logger;

extern crate structopt;
use structopt::StructOpt;

use candid::parser::types::IDLType;
use candid::parser::typing::{check_type, Env, TypeEnv};

use candiff::{
    //Type,
    pretty,
    Value,
};

/// candiff
#[derive(StructOpt, Debug)]
#[structopt(name = "candiff", setting = clap::AppSettings::DeriveDisplayOrder)]
struct CliOpt {
    /// Enable tracing -- the most verbose log.
    #[structopt(short = "t", long = "trace-log")]
    log_trace: bool,
    /// Enable logging for debugging.
    #[structopt(short = "d", long = "debug-log")]
    log_debug: bool,
    /// Disable most logging, if not explicitly enabled.
    #[structopt(short = "q", long = "quiet-log")]
    log_quiet: bool,
    #[structopt(subcommand)]
    command: CliCommand,
}
#[derive(StructOpt, Debug)]
enum CliFormat {
    #[structopt(name = "text", about = "textual format.")]
    Text,
}

impl FromStr for CliFormat {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "text" => Ok(CliFormat::Text),
            s => Err(format!("format not recognized: {}", s)),
        }
    }
}

#[derive(StructOpt, Debug)]
enum CliCommand {
    #[structopt(
        name = "echo",
        about = "Pretty print a single value in a standard way."
    )]
    EchoValue {
        /// Input format
        #[structopt(short = "i", long = "input-format", default_value = "text")]
        format: CliFormat,
        input: String,
        /// Optional input type
        #[structopt(short = "t", long = "input-type")]
        input_type: Option<String>,
        /// Output format uses Debug formatter
        #[structopt(short = "d", long = "debug-output")]
        debug_output: bool,
    },

    #[structopt(name = "diff", about = "Difference two values, giving an edit.")]
    DiffValue {
        /// Input format
        #[structopt(short = "i", long = "input-format", default_value = "text")]
        format: CliFormat,
        input1: String,
        input2: String,
        /// Optional (common) input type
        #[structopt(short = "t", long = "input-type")]
        input_type: Option<String>,
        /// Output format uses Debug formatter
        #[structopt(short = "d", long = "debug-output")]
        debug_output: bool,
    },

    #[structopt(
        name = "completions",
        about = "Generate shell scripts for candiff subcommand auto-completions."
    )]
    Completions { shell: Shell },
}

fn init_log(level_filter: log::LevelFilter) {
    use env_logger::{Builder, WriteStyle};
    let mut builder = Builder::new();
    builder
        .filter(None, level_filter)
        .write_style(WriteStyle::Always)
        .init();
}

fn main() {
    let mut type_consistency_holds = true;
    let cliopt = CliOpt::from_args();
    init_log(
        match (cliopt.log_trace, cliopt.log_debug, cliopt.log_quiet) {
            (true, _, _) => log::LevelFilter::Trace,
            (_, true, _) => log::LevelFilter::Debug,
            (_, _, true) => log::LevelFilter::Error,
            (_, _, _) => log::LevelFilter::Info,
        },
    );
    trace!("{:?}", &cliopt.command);
    match cliopt.command {
        CliCommand::EchoValue {
            format,
            input,
            input_type,
            debug_output,
        } => {
            match format {
                CliFormat::Text => {
                    let ty = match input_type {
                        None => {
                            warn!("No input type provided; All numbers remain textual.");
                            None
                        }
                        Some(t) => match t.parse::<IDLType>() {
                            Ok(ty) => {
                                trace!("input_type = {:?}", ty);
                                Some(ty)
                            }
                            Err(e) => {
                                error!("{}", e);
                                None
                            }
                        },
                    };
                    match Value::from_str(&input) {
                        Ok(v) => {
                            // check the type, and then annotate the value with that type, possibly transforming it
                            let v = match ty {
                                None => v,
                                Some(ty) => {
                                    // to do -- check a program file and get the type env
                                    let te = &mut TypeEnv::new();
                                    trace!("check_type ...");
                                    match check_type(&Env { te, pre: false }, &ty) {
                                        Err(e) => {
                                            error!("{}", e);
                                            type_consistency_holds = false;
                                            v
                                        }
                                        Ok(ty) => {
                                            trace!("annotate_type ...");
                                            match v.annotate_type(true, &TypeEnv::new(), &ty) {
                                                Ok(v) => v,
                                                Err(e) => {
                                                    type_consistency_holds = false;
                                                    error!("{}", e);
                                                    v
                                                }
                                            }
                                        }
                                    }
                                }
                            };
                            trace!("{:?}", v);
                            if debug_output {
                                println!("{:?}", v)
                            } else {
                                println!("{}", v)
                            }
                        }
                        Err(e) => error!("{}", e),
                    }
                }
            }
        }
        CliCommand::DiffValue {
            format,
            input1,
            input2,
            input_type,
            debug_output,
        } => {
            match format {
                CliFormat::Text => {
                    match (Value::from_str(&input1), Value::from_str(&input2)) {
                        (Err(e1), Err(e2)) => error!(
                            "Both values failed to parse:\nFirst: {}\nSecond: {}",
                            e1, e2
                        ),
                        (Err(e1), _) => error!("First value failed to parse (only): {}\n", e1),
                        (_, Err(e2)) => error!("Second value failed to parse (only): {}\n", e2),
                        (Ok(v1), Ok(v2)) => {
                            let input_type = match input_type {
                                None => {
                                    warn!("No input type provided; All numbers remain textual.");
                                    None
                                }
                                Some(t) => match t.parse::<IDLType>() {
                                    Ok(ty) => {
                                        trace!("input_type = {:?}", ty);
                                        Some(ty)
                                    }
                                    Err(e) => {
                                        error!("{}", e);
                                        None
                                    }
                                },
                            };
                            trace!("value_1 = {:?}", v1);
                            trace!("value_2 = {:?}", v2);
                            // check the type, and then annotate the value with that type, possibly transforming it
                            let (v1, v2, input_type) = match input_type {
                                None => (v1, v2, None),
                                Some(ty) => {
                                    // to do -- check a program file and get the type env
                                    let te = &mut TypeEnv::new();
                                    trace!("check_type ...");
                                    match check_type(&Env { te, pre: false }, &ty) {
                                        Err(e) => {
                                            type_consistency_holds = false;
                                            error!("{}", e);
                                            (v1, v2, None)
                                        }
                                        Ok(ty) => {
                                            trace!("annotate_type for first value ...");
                                            let v1 = match v1.annotate_type(
                                                true,
                                                &TypeEnv::new(),
                                                &ty,
                                            ) {
                                                Ok(v) => v,
                                                Err(e) => {
                                                    type_consistency_holds = false;
                                                    error!("{}", e);
                                                    v1
                                                }
                                            };
                                            trace!("annotate_type for second value ...");
                                            let v2 = match v2.annotate_type(
                                                true,
                                                &TypeEnv::new(),
                                                &ty,
                                            ) {
                                                Ok(v) => v,
                                                Err(e) => {
                                                    type_consistency_holds = false;
                                                    error!("{}", e);
                                                    v2
                                                }
                                            };
                                            (v1, v2, Some(ty))
                                        }
                                    }
                                }
                            };
                            trace!("annotated_value_1 = {:?}", v1);
                            trace!("annotated_value_2 = {:?}", v2);
                            let edit = candiff::value_diff(&v1, &v2, &input_type);
                            trace!("value_diff = {:?}", edit.0);
                            if candiff::value_edit_is_skip(&edit) {
                                debug!("equal values; no change.")
                            } else if debug_output {
                                println!("{:?}", edit.0)
                            } else {
                                println!("{}", pretty::value_edit(&edit).pretty(80))
                            }
                        }
                    }
                }
            }
        }
        CliCommand::Completions { shell: s } => {
            // see also: https://clap.rs/effortless-auto-completion/
            //
            CliOpt::clap().gen_completions_to("candiff", s, &mut std::io::stdout());
            info!("done")
        }
    }

    // did we find a type error? if so, give error code.
    std::process::exit(if type_consistency_holds { 0 } else { -1 })
}
