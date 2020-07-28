extern crate clap;
use clap::Shell;
use std::str::FromStr;

// Logging:
#[macro_use]
extern crate log;
extern crate env_logger;

extern crate structopt;
use structopt::StructOpt;

use candid_diff::Value;

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
    #[structopt(name = "echo", about = "Pretty print a single value.")]
    EchoValue{
        /// Input format
        #[structopt(short = "i", long = "input-format", default_value = "text")]
        format: CliFormat,
        input: String,
    },

    #[structopt(name = "diff", about = "Difference two values, giving an edit.")]
    DiffValue,

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
    info!("Evaluating CLI command: {:?} ...", &cliopt.command);
    // - - - - - - - - - - -
    match cliopt.command {
        CliCommand::EchoValue{ format, input } => {
            trace!("echo {:?} {}", format, input);
            match format {
                CliFormat::Text => {
                    match Value::from_str(&input) {
                        Ok(v) => {
                            println!("{}", v)
                        },
                        Err(e) => {
                            eprintln!("{}", e)
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
        CliCommand::DiffValue => {
            unimplemented!()
        }
        CliCommand::Completions { shell: s } => {
            // see also: https://clap.rs/effortless-auto-completion/
            //
            CliOpt::clap().gen_completions_to("candiff", s, &mut std::io::stdout());
            info!("done")
        }
    }
}

#[test]
fn test_cli_help() {
    use assert_cmd::Command;
    let mut cmd = Command::cargo_bin("candiff").unwrap();
    cmd.arg("help");
    cmd.assert().success();
}

#[test]
fn test_cli_echo_nat() {
    use predicates::prelude::*;
    use assert_cmd::Command;
    let mut cmd = Command::cargo_bin("candiff").unwrap();
    cmd.arg("echo").arg("1");
    cmd.assert()
        .stdout(predicate::eq(b"1\n" as &[u8]))
        .success();
}

#[test]
fn test_cli_echo_vec_nat() {
    use predicates::prelude::*;
    use assert_cmd::Command;
    let mut cmd = Command::cargo_bin("candiff").unwrap();
    cmd.arg("echo").arg("vec {1; 2}");
    cmd.assert()
        .stdout(predicate::eq(b"vec { 1; 2; }\n" as &[u8]))
        .success();
}

#[test]
fn test_cli_echo_variant_num() {
    use predicates::prelude::*;
    use assert_cmd::Command;
    let mut cmd = Command::cargo_bin("candiff").unwrap();
    cmd.arg("echo").arg("variant { 1 = 2 }");
    cmd.assert()
        .stdout(predicate::eq(b"variant { 1 = 2 }\n" as &[u8]))
        .success();
}

#[test]
fn test_cli_echo_variant_label() {
    use predicates::prelude::*;
    use assert_cmd::Command;
    let mut cmd = Command::cargo_bin("candiff").unwrap();
    cmd.arg("echo").arg("variant { xyz = 2 }");
    cmd.assert()
        .stdout(predicate::eq(b"variant { xyz = 2 }\n" as &[u8]))
        .success();
}
