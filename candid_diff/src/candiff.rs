extern crate clap;
use clap::Shell;

// Logging:
#[macro_use]
extern crate log;
extern crate env_logger;

extern crate structopt;
use structopt::StructOpt;

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
enum CliCommand {
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
