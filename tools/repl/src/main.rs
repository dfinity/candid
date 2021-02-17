use ansi_term::Color;
use candid::{
    check_prog, pretty_parse,
    types::{Function, Type},
    IDLArgs, IDLProg, TypeEnv,
};
use candid::{Decode, Encode};
use ic_agent::export::Principal;
use ic_agent::Agent;
use rustyline::completion::{extract_word, Completer, FilenameCompleter, Pair};
use rustyline::error::ReadlineError;
use rustyline::highlight::{Highlighter, MatchingBracketHighlighter};
use rustyline::hint::{Hinter, HistoryHinter};
use rustyline::validate::{self, MatchingBracketValidator, Validator};
use rustyline::{CompletionType, Config, Context, Editor};
use rustyline_derive::Helper;
use std::borrow::Cow::{self, Borrowed, Owned};
use std::cell::RefCell;
use std::collections::BTreeMap;

#[derive(Default)]
struct CanisterMap(BTreeMap<Principal, CanisterInfo>);
#[derive(Clone)]
struct CanisterInfo {
    pub env: TypeEnv,
    pub methods: BTreeMap<String, Function>,
}
impl CanisterMap {
    fn get(&mut self, id: &Principal) -> anyhow::Result<&CanisterInfo> {
        if !self.0.contains_key(id) {
            let info = fetch_actor(id)?;
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
    fn get_func(&self, method: &str) -> Option<&Function> {
        self.methods.get(method)
    }
}

#[tokio::main]
async fn fetch_actor(canister_id: &Principal) -> anyhow::Result<CanisterInfo> {
    let agent = Agent::builder().with_url("http://localhost:8000").build()?;
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
        .into_iter()
        .map(|(meth, ty)| {
            let func = env.as_func(ty).unwrap();
            (meth.to_owned(), func.clone())
        })
        .collect();
    Ok(CanisterInfo { env, methods })
}

#[derive(Helper)]
struct MyHelper {
    completer: FilenameCompleter,
    highlighter: MatchingBracketHighlighter,
    validator: MatchingBracketValidator,
    hinter: HistoryHinter,
    colored_prompt: String,
    canister_map: RefCell<CanisterMap>,
}

fn random_value(env: &TypeEnv, tys: &[Type]) -> candid::Result<IDLArgs> {
    use candid::parser::configs::Configs;
    use rand::Rng;
    let mut rng = rand::thread_rng();
    let seed: Vec<_> = (0..2048).map(|_| rng.gen::<u8>()).collect();
    let config = Configs::from_dhall("{=}")?;
    IDLArgs::any(&seed, &config, env, &tys)
}

// Return position at the end of principal, principal, and method
fn extract_canister(line: &str, pos: usize) -> Option<(usize, Principal, &str)> {
    let (id_pos, word) = extract_word(line, pos, None, b" ");
    let (pos, id, meth) = match word.rfind('.') {
        Some(idx) => (id_pos + idx, &word[..idx], &word[idx + 1..]),
        None => (pos, word, ""),
    };
    let canister_id = Principal::from_text(id).ok()?;
    Some((pos, canister_id, meth))
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
            Some((pos, canister_id, meth)) => {
                let mut map = self.canister_map.borrow_mut();
                Ok(match map.get(&canister_id) {
                    Ok(info) => (pos, info.match_method(meth)),
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
        match extract_canister(line, pos) {
            Some((_, canister_id, method)) => {
                let mut map = self.canister_map.borrow_mut();
                match map.get(&canister_id) {
                    Ok(info) => {
                        let func = info.get_func(method)?;
                        let value = random_value(&info.env, &func.args).ok()?;
                        Some(format!("{}", value))
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
        let s = format!("{}", Color::Black.dimmed().paint(hint));
        Owned(s.to_owned())
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

fn print_eval(v: Result<IDLArgs, candid::Error>) {
    match v {
        Ok(res) => println!("{}", res),
        Err(e) => eprintln!("Error: {}", e),
    }
}

fn repl() {
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
    };
    let mut rl = Editor::with_config(config);
    rl.set_helper(Some(h));
    if rl.load_history("./.history").is_err() {
        eprintln!("No history found");
    }
    let mut count = 1;
    loop {
        let p = format!("{}> ", count);
        rl.helper_mut().expect("No helper").colored_prompt =
            format!("{}", Color::Green.bold().paint(&p));
        let input = rl.readline(&p);
        match input {
            Ok(line) => {
                rl.add_history_entry(&line);
                print_eval(pretty_parse::<IDLArgs>("stdin", &line));
            }
            Err(ReadlineError::Interrupted) | Err(ReadlineError::Eof) => break,
            Err(err) => {
                eprintln!("Error: {:?}", err);
                break;
            }
        }
        count += 1;
    }
    rl.save_history("./.history").unwrap();
}

fn main() {
    repl()
}
