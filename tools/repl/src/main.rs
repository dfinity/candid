use ansi_term::Color;
use ic_agent::Agent;
use rustyline::error::ReadlineError;
use rustyline::CompletionType;
use tokio::runtime::Runtime;

mod command;
mod grammar;
mod helper;
mod token;
use crate::command::Command;
use crate::helper::MyHelper;

fn unwrap<T, E: std::fmt::Display, F>(v: Result<T, E>, f: F)
where
    E: std::fmt::Display,
    F: FnOnce(T),
{
    match v {
        Ok(res) => f(res),
        Err(e) => eprintln!("Error: {}", e),
    }
}

fn repl(opts: Opts) -> anyhow::Result<()> {
    let replica = opts.replica.unwrap_or_else(|| "local".to_string());
    let url = match replica.as_str() {
        "local" => "http://localhost:8000/",
        "ic" => "https://gw.dfinity.network",
        url => url,
    };
    println!("Ping {}...", url);
    let agent = Agent::builder().with_url(url).build()?;
    {
        let mut runtime = Runtime::new().expect("Unable to create a runtime");
        runtime.block_on(agent.fetch_root_key())?;
    }

    println!("Canister REPL");
    let config = rustyline::Config::builder()
        .history_ignore_space(true)
        .completion_type(CompletionType::List)
        .build();
    let h = MyHelper::new(agent);
    let mut rl = rustyline::Editor::with_config(config);
    rl.set_helper(Some(h));
    if rl.load_history("./.history").is_err() {
        eprintln!("No history found");
    }
    let mut count = 1;
    loop {
        let p = format!("{} {}> ", replica, count);
        rl.helper_mut().unwrap().colored_prompt = format!("{}", Color::Green.bold().paint(&p));
        let input = rl.readline(&p);
        match input {
            Ok(line) => {
                rl.add_history_entry(&line);
                unwrap(line.parse::<Command>(), |cmd| {
                    let mut helper = rl.helper_mut().unwrap();
                    helper.history.push(line.clone());
                    unwrap(cmd.run(&mut helper), |_| {});
                });
            }
            Err(ReadlineError::Interrupted) | Err(ReadlineError::Eof) => break,
            Err(err) => {
                eprintln!("Error: {:?}", err);
                break;
            }
        }
        count += 1;
    }
    rl.save_history("./.history")?;
    Ok(())
}

use structopt::StructOpt;
#[derive(StructOpt)]
#[structopt(global_settings = &[structopt::clap::AppSettings::ColoredHelp, structopt::clap::AppSettings::DeriveDisplayOrder])]
struct Opts {
    #[structopt(short, long)]
    replica: Option<String>,
}

fn main() -> anyhow::Result<()> {
    let opts = Opts::from_args();
    repl(opts)
}
