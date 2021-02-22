use ansi_term::Color;
use anyhow::anyhow;
use candid::{
    check_prog,
    parser::configs::Configs,
    parser::value::IDLValue,
    pretty_parse,
    types::{Function, Type},
    Decode, Encode, IDLArgs, IDLProg, TypeEnv,
};
use ic_agent::export::Principal;
use ic_agent::Agent;
use rustyline::completion::{Completer, FilenameCompleter, Pair};
use rustyline::error::ReadlineError;
use rustyline::highlight::{Highlighter, MatchingBracketHighlighter};
use rustyline::hint::{Hinter, HistoryHinter};
use rustyline::validate::{self, MatchingBracketValidator, Validator};
use rustyline::{CompletionType, Config, Context, Editor};
use rustyline_derive::Helper;
use std::borrow::Cow::{self, Borrowed, Owned};
use std::cell::RefCell;
use std::collections::BTreeMap;
use tokio::runtime::Runtime;

mod command;
mod grammar;
mod token;
use crate::command::Command;

#[derive(Default)]
struct CanisterMap(BTreeMap<Principal, CanisterInfo>);
#[derive(Clone)]
struct CanisterInfo {
    pub env: TypeEnv,
    pub methods: BTreeMap<String, Function>,
}
impl CanisterMap {
    fn get(&mut self, agent: &Agent, id: &Principal) -> anyhow::Result<&CanisterInfo> {
        if !self.0.contains_key(id) {
            let info = fetch_actor(agent, id)?;
            self.0.insert(id.clone(), info);
        }
        Ok(self.0.get(id).unwrap())
    }
}

impl CanisterInfo {
    fn match_method(&self, meth: &str) -> Vec<Pair> {
        self.methods
            .iter()
            .filter(|(name, _)| name.starts_with(meth))
            .map(|(meth, func)| Pair {
                display: format!("{} : {}", meth, func),
                replacement: format!(".{}", meth),
            })
            .collect()
    }
}

#[tokio::main]
async fn fetch_actor(agent: &Agent, canister_id: &Principal) -> anyhow::Result<CanisterInfo> {
    let response = agent
        .query(canister_id, "__get_candid_interface_tmp_hack")
        .with_arg(&Encode!()?)
        .call()
        .await?;
    let response = Decode!(&response, String)?;
    let ast = pretty_parse::<IDLProg>("fetched candid", &response)?;
    let mut env = TypeEnv::new();
    let actor = check_prog(&mut env, &ast)?.unwrap();
    let methods = env
        .as_service(&actor)?
        .iter()
        .map(|(meth, ty)| {
            let func = env.as_func(ty).unwrap();
            (meth.to_owned(), func.clone())
        })
        .collect();
    Ok(CanisterInfo { env, methods })
}

#[tokio::main]
async fn call(
    agent: &Agent,
    canister_id: &Principal,
    method: &str,
    args: &IDLArgs,
    env: &TypeEnv,
    func: &Function,
) -> anyhow::Result<IDLArgs> {
    let args = args.to_bytes_with_types(env, &func.args)?;
    let bytes = if func.is_query() {
        agent
            .query(canister_id, method)
            .with_arg(args)
            .call()
            .await?
    } else {
        let waiter = delay::Delay::builder()
            .exponential_backoff(std::time::Duration::from_secs(1), 1.1)
            .timeout(std::time::Duration::from_secs(60 * 5))
            .build();
        agent
            .update(canister_id, method)
            .with_arg(args)
            .call_and_wait(waiter)
            .await?
    };
    Ok(IDLArgs::from_bytes_with_types(&bytes, env, &func.rets)?)
}

#[derive(Helper)]
struct MyHelper {
    completer: FilenameCompleter,
    highlighter: MatchingBracketHighlighter,
    validator: MatchingBracketValidator,
    hinter: HistoryHinter,
    colored_prompt: String,
    canister_map: RefCell<CanisterMap>,
    agent: Agent,
    config: Configs,
}

fn random_value(
    env: &TypeEnv,
    tys: &[Type],
    given_args: &[IDLValue],
    config: &Configs,
) -> candid::Result<String> {
    use rand::Rng;
    let mut rng = rand::thread_rng();
    let seed: Vec<_> = (0..2048).map(|_| rng.gen::<u8>()).collect();
    let result = IDLArgs::any(&seed, &config, env, &tys)?;
    Ok(if !given_args.is_empty() {
        if given_args.len() <= tys.len() {
            let mut res = String::new();
            for v in result.args[given_args.len()..].iter() {
                res.push_str(&format!(", {}", v));
            }
            res.push(')');
            res
        } else {
            "".to_owned()
        }
    } else {
        format!("{}", result)
    })
}

// Return position at the end of principal, principal, method, args
fn extract_canister(line: &str, pos: usize) -> Option<(usize, Principal, String, Vec<IDLValue>)> {
    let command = line[..pos].parse::<Command>().ok()?;
    match command {
        Command::Call {
            canister,
            method,
            args,
        } => Some((canister.span.end, canister.value, method, args)),
        _ => None,
    }
}

impl Completer for MyHelper {
    type Candidate = Pair;
    fn complete(
        &self,
        line: &str,
        pos: usize,
        ctx: &Context<'_>,
    ) -> Result<(usize, Vec<Pair>), ReadlineError> {
        match extract_canister(line, pos) {
            Some((pos, canister_id, meth, _)) => {
                let mut map = self.canister_map.borrow_mut();
                Ok(match map.get(&self.agent, &canister_id) {
                    Ok(info) => (pos, info.match_method(&meth)),
                    Err(_) => (pos, Vec::new()),
                })
            }
            None => self.completer.complete(line, pos, ctx),
        }
    }
}

impl Hinter for MyHelper {
    type Hint = String;
    fn hint(&self, line: &str, pos: usize, ctx: &Context<'_>) -> Option<String> {
        if pos < line.len() {
            return None;
        }
        match extract_canister(line, pos) {
            Some((_, canister_id, method, args)) => {
                let mut map = self.canister_map.borrow_mut();
                match map.get(&self.agent, &canister_id) {
                    Ok(info) => {
                        let func = info.methods.get(&method)?;
                        let value =
                            random_value(&info.env, &func.args, &args, &self.config).ok()?;
                        Some(value)
                    }
                    Err(_) => None,
                }
            }
            None => self.hinter.hint(line, pos, ctx),
        }
    }
}

impl Highlighter for MyHelper {
    fn highlight_prompt<'b, 's: 'b, 'p: 'b>(
        &'s self,
        prompt: &'p str,
        default: bool,
    ) -> Cow<'b, str> {
        if default {
            Borrowed(&self.colored_prompt)
        } else {
            Borrowed(prompt)
        }
    }

    fn highlight_hint<'h>(&self, hint: &'h str) -> Cow<'h, str> {
        let s = format!("{}", Color::White.dimmed().paint(hint));
        Owned(s)
    }

    fn highlight<'l>(&self, line: &'l str, pos: usize) -> Cow<'l, str> {
        self.highlighter.highlight(line, pos)
    }

    fn highlight_char(&self, line: &str, pos: usize) -> bool {
        self.highlighter.highlight_char(line, pos)
    }
}

impl Validator for MyHelper {
    fn validate(
        &self,
        ctx: &mut validate::ValidationContext,
    ) -> rustyline::Result<validate::ValidationResult> {
        self.validator.validate(ctx)
    }

    fn validate_while_typing(&self) -> bool {
        self.validator.validate_while_typing()
    }
}

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
fn run(helper: &mut MyHelper, cmd: Command) -> anyhow::Result<()> {
    match cmd {
        Command::Call {
            canister,
            method,
            args,
        } => {
            let canister_id = canister.value;
            let agent = &helper.agent;
            let mut map = helper.canister_map.borrow_mut();
            let info = map.get(&agent, &canister_id)?;
            let func = info
                .methods
                .get(&method)
                .ok_or_else(|| anyhow!("no method {}", method))?;
            let args = IDLArgs { args };
            let res = call(&agent, &canister_id, &method, &args, &info.env, &func)?;
            println!("{}", res);
        }
        Command::Config(conf) => helper.config = Configs::from_dhall(&conf)?,
    }
    Ok(())
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
    let config = Config::builder()
        .history_ignore_space(true)
        .completion_type(CompletionType::List)
        .build();
    let h = MyHelper {
        completer: FilenameCompleter::new(),
        highlighter: MatchingBracketHighlighter::new(),
        hinter: HistoryHinter {},
        colored_prompt: "".to_owned(),
        validator: MatchingBracketValidator::new(),
        canister_map: RefCell::new(CanisterMap::default()),
        config: Configs::from_dhall("{=}")?,
        agent,
    };
    let mut rl = Editor::with_config(config);
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
                    unwrap(run(&mut helper, cmd), |_| {});
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
