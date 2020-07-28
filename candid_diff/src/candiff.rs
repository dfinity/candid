extern crate clap;
use clap::Shell;
use std::str::FromStr;

// Logging:
#[macro_use]
extern crate log;
extern crate env_logger;

extern crate structopt;
use structopt::StructOpt;

use candid::parser::typing::{check_type, Env, TypeEnv};
use candid::parser::types::IDLType;

use candid_diff::{
    //Type,
    Value};

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
    #[structopt(name = "raw", about = "raw (binary, non-textual) format.")]
    Raw,

    #[structopt(name = "text", about = "textual format.")]
    Text,
}

impl FromStr for CliFormat {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "raw" => Ok(CliFormat::Raw),
            "text" => Ok(CliFormat::Text),
            s => Err(format!("format not recognized: {}", s))

        }
    }
}

#[derive(StructOpt, Debug)]
enum CliCommand {
    #[structopt(name = "echo", about = "Pretty print a single value in a standard way.")]
    EchoValue {
        /// Input format
        #[structopt(short = "i", long = "input-format", default_value = "text")]
        format: CliFormat,
        input: String,
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
        CliCommand::EchoValue{ format, input, input_type, debug_output } => {
            match format {
                CliFormat::Text => {
                    let ty = match input_type {
                        None => {
                            warn!("No input type provided; All numbers remain textual.");
                            None
                        }
                        Some(t) => match t.parse::<IDLType>() {
                            Ok(ty) => { trace!("input_type = {:?}", ty); Some(ty) }
                            Err(e) => { error!("{}", e); None }
                        }
                    };
                    match Value::from_str(&input) {
                        Ok(v) => {
                            // check the type, and then annotate the value with that type, possibly transforming it
                            let v = match ty {
                                None => { v }
                                Some(ty) => {
                                    // to do -- check a program file and get the type env
                                    let te = &mut TypeEnv::new();
                                    trace!("check_type ...");
                                    match check_type(&Env{te, pre:false}, &ty) {
                                        Err(e) => {
                                            error!("{}", e); v
                                        }
                                        Ok(ty) => {
                                            trace!("annotate_type ...");
                                            match v.annotate_type(&TypeEnv::new(), &ty) {
                                                Ok(v) => v,
                                                Err(e) => {
                                                    error!("{}", e); v
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
                        },
                        Err(e) => {
                            error!("{}", e)
                        }
                    }
                },
                CliFormat::Raw => {
                    // how is it encoded as a string?
                    // base64?
                    // always take binary from stdin?
                    // something else?
                    unimplemented!()
                }
            }
        }
        CliCommand::DiffValue{ format, input1, input2 } => {
            match format {
                CliFormat::Text => {
                    match (Value::from_str(&input1),
                           Value::from_str(&input2)) {
                        (Err(e1), Err(e2)) => { error!("Both values failed to parse:\nFirst: {}\nSecond: {}", e1, e2) },
                        (Err(e1), _) => { error!("First value failed to parse (only): {}\n", e1) },
                        (_, Err(e2)) => { error!("Second value failed to parse (only): {}\n", e2) },
                        (Ok(v1), Ok(v2)) => {
                            trace!("value_1 = {:?}", v1);
                            trace!("value_2 = {:?}", v2);
                            let edit = candid_diff::value_diff(&v1, &v2, None);
                            trace!("value_diff = {:?}", edit.0);
                            if candid_diff::value_edit_is_skip(&edit) {
                                debug!("equal values; no change.")
                            } else {
                                // to do -- more minimal textual output format for edits
                                println!("{:?}", edit.0)
                            }
                        }
                    }
                }
                CliFormat::Raw => {
                    // how is it encoded as a string?
                    // base64?
                    // always take binary from stdin?
                    // something else?
                    unimplemented!()
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
}

/// Unit tests for command line interface (move elsewhere?)
#[cfg(test)]
mod candiff_cli {
    use predicates::prelude::*;
    use assert_cmd::Command;

    #[test]
    fn help() {
        let mut cmd = Command::cargo_bin("candiff").unwrap();
        cmd.arg("help");
        cmd.assert().success();
    }

    fn candiff() -> Command {
        Command::cargo_bin("candiff").unwrap()
    }
    
    mod echo {
        use super::*;

        #[test]
        fn number() {
            let mut cmd = candiff();
            cmd.arg("echo").arg("1");
            cmd.assert()
                .stdout(predicate::eq(b"1\n" as &[u8]))
                .success();
        }

        #[test]
        fn number_debug() {
            let mut cmd = candiff();
            cmd.arg("echo").arg("1").arg("-d");
            cmd.assert()
                .stdout(predicate::eq(b"Number(\"1\")\n" as &[u8]))
                .success();
        }

        #[test]
        fn nat_debug() {
            let mut cmd = candiff();
            cmd.arg("echo").arg("1").arg("-t nat").arg("-d");
            cmd.assert()
                .stdout(predicate::eq(b"Nat(Nat(BigUint { data: [1] }))\n" as &[u8]))
                .success();
        }

        #[test]
        fn int_debug() {
            let mut cmd = candiff();
            cmd.arg("echo").arg("1").arg("-t int").arg("-d");
            cmd.assert()
                .stdout(predicate::eq(b"Int(Int(BigInt { sign: Plus, data: BigUint { data: [1] } }))\n" as &[u8]))
                .success();
        }

        #[test]
        fn vec_num() {
            let mut cmd = candiff();
            cmd.arg("echo").arg("vec {1; 2}");
            cmd.assert()
                .stdout(predicate::eq(b"vec { 1; 2; }\n" as &[u8]))
                .success();
        }

        #[test]
        fn variant_num() {
            let mut cmd = candiff();
            cmd.arg("echo").arg("variant { 1 = 2 }");
            cmd.assert()
                .stdout(predicate::eq(b"variant { 1 = 2 }\n" as &[u8]))
                .success();
        }

        #[test]
        fn variant_label() {
            let mut cmd = candiff();
            cmd.arg("echo").arg("variant { xyz = 2 }");
            cmd.assert()
                .stdout(predicate::eq(b"variant { xyz = 2 }\n" as &[u8]))
                .success();
        }
    }

    mod diff {
        use super::*;

        #[test]
        fn true_true() {
            let mut cmd = candiff();
            cmd.arg("diff").arg("true").arg("true");
            cmd.assert()
                .stdout(predicate::eq(b"" as &[u8]))
                .success();
        }

        #[test]
        fn true_false() {
            let mut cmd = candiff();
            cmd.arg("diff").arg("true").arg("false");
            cmd.assert()
                .stdout(predicate::eq(b"Put(Bool(false))\n" as &[u8]))
                .success();
        }

        #[test]
        fn false_true() {
            let mut cmd = candiff();
            cmd.arg("diff").arg("false").arg("true");
            cmd.assert()
                .stdout(predicate::eq(b"Put(Bool(true))\n" as &[u8]))
                .success();
        }

        #[test]
        fn one_one() {
            let mut cmd = candiff();
            cmd.arg("diff").arg("1").arg("1");
            cmd.assert()
                .stdout(predicate::eq(b"" as &[u8]))
                .success();
        }

        #[test]
        fn one_two() {
            let mut cmd = candiff();
            cmd.arg("diff").arg("1").arg("2");
            cmd.assert()
                .stdout(predicate::eq(b"Put(Number(\"2\"))\n" as &[u8]))
                .success();
        }

        #[test]
        fn null_null() {
            let mut cmd = candiff();
            cmd.arg("diff").arg("null").arg("null");
            cmd.assert()
                .stdout(predicate::eq(b"" as &[u8]))
                .success();
        }

        #[test]
        fn text_empty_empty() {
            let mut cmd = candiff();
            cmd.arg("diff").arg("\"\"").arg("\"\"");
            cmd.assert()
                .stdout(predicate::eq(b"" as &[u8]))
                .success();
        }

        #[test]
        fn text_a_text_b() {
            let mut cmd = candiff();
            cmd.arg("diff").arg("\"a\"").arg("\"b\"");
            cmd.assert()
                .stdout(predicate::eq(b"Put(Text(\"b\"))\n" as &[u8]))
                .success();
        }
    }
}
