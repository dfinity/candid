use crate::command::{extract_canister, Value};
use ansi_term::Color;
use candid::{
    check_prog,
    parser::configs::Configs,
    parser::value::IDLValue,
    pretty_parse,
    types::{Function, Type},
    Decode, Encode, IDLArgs, IDLProg, Principal, TypeEnv,
};
use ic_agent::Agent;
use rustyline::completion::{Completer, FilenameCompleter, Pair};
use rustyline::error::ReadlineError;
use rustyline::highlight::{Highlighter, MatchingBracketHighlighter};
use rustyline::hint::{Hinter, HistoryHinter};
use rustyline::validate::{self, MatchingBracketValidator, Validator};
use rustyline::Context;
use rustyline_derive::Helper;
use std::borrow::Cow::{self, Borrowed, Owned};
use std::cell::RefCell;
use std::collections::BTreeMap;

#[derive(Default)]
pub struct CanisterMap(BTreeMap<Principal, CanisterInfo>);
#[derive(Default)]
pub struct Env(pub BTreeMap<String, IDLValue>);
#[derive(Default)]
pub struct NameEnv(pub BTreeMap<String, Principal>);
#[derive(Clone)]
pub struct CanisterInfo {
    pub env: TypeEnv,
    pub methods: BTreeMap<String, Function>,
}
impl CanisterMap {
    pub fn get(&mut self, agent: &Agent, id: &Principal) -> anyhow::Result<&CanisterInfo> {
        if !self.0.contains_key(id) {
            let info = fetch_actor(agent, id)?;
            self.0.insert(id.clone(), info);
        }
        Ok(self.0.get(id).unwrap())
    }
}
impl CanisterInfo {
    pub fn match_method(&self, meth: &str) -> Vec<Pair> {
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

#[derive(Helper)]
pub struct MyHelper {
    completer: FilenameCompleter,
    highlighter: MatchingBracketHighlighter,
    validator: MatchingBracketValidator,
    hinter: HistoryHinter,
    pub colored_prompt: String,
    pub canister_map: RefCell<CanisterMap>,
    pub agent_url: String,
    pub agent: Agent,
    pub config: Configs,
    pub env: Env,
    pub canister_env: NameEnv,
    pub history: Vec<String>,
}

impl MyHelper {
    pub fn new(agent: Agent, agent_url: String) -> Self {
        MyHelper {
            completer: FilenameCompleter::new(),
            highlighter: MatchingBracketHighlighter::new(),
            hinter: HistoryHinter {},
            colored_prompt: "".to_owned(),
            validator: MatchingBracketValidator::new(),
            canister_map: RefCell::new(CanisterMap::default()),
            config: Configs::from_dhall("{=}").unwrap(),
            env: Env::default(),
            canister_env: NameEnv::default(),
            history: Vec::new(),
            agent,
            agent_url,
        }
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
        match extract_canister(line, pos, &self.canister_env) {
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
        match extract_canister(line, pos, &self.canister_env) {
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

fn random_value(
    env: &TypeEnv,
    tys: &[Type],
    given_args: &[Value],
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
