use super::helper::{Env, MyHelper, NameEnv};
use super::token::{ParserError, Spanned, Tokenizer};
use anyhow::anyhow;
use candid::Principal;
use candid::{
    parser::configs::Configs, parser::value::IDLValue, types::Function, IDLArgs, TypeEnv,
};
use ic_agent::Agent;

#[derive(Debug, Clone)]
pub enum Value {
    Candid(IDLValue),
    Path(Vec<String>),
}
impl Value {
    fn get<'a>(&'a self, env: &'a Env) -> anyhow::Result<&'a IDLValue> {
        Ok(match self {
            Value::Candid(v) => v,
            Value::Path(vs) => env
                .0
                .get(&vs[0])
                .ok_or_else(|| anyhow!("Undefined variable {}", vs[0]))?,
        })
    }
}

#[derive(Debug, Clone)]
pub enum Command {
    Call {
        canister: Spanned<String>,
        method: String,
        args: Vec<Value>,
    },
    Config(String),
    Show(Value),
    Let(String, Value),
    Assert(Value, Value),
    Export(String),
    Identity(String),
}

impl Command {
    pub fn run(&self, helper: &mut MyHelper) -> anyhow::Result<()> {
        match self {
            Command::Call {
                canister,
                method,
                args,
            } => {
                let try_id = Principal::from_text(&canister.value);
                let canister_id = match try_id {
                    Ok(ref id) => id,
                    Err(_) => helper
                        .canister_env
                        .0
                        .get(&canister.value)
                        .ok_or_else(|| anyhow!("Unknown canister {}", canister.value))?,
                };
                let agent = &helper.agent;
                let mut map = helper.canister_map.borrow_mut();
                let info = map.get(&agent, canister_id)?;
                let func = info
                    .methods
                    .get(method)
                    .ok_or_else(|| anyhow!("no method {}", method))?;
                let mut values = Vec::new();
                for arg in args.iter() {
                    values.push(arg.get(&helper.env)?.clone());
                }
                let args = IDLArgs { args: values };
                let res = call(&agent, canister_id, &method, &args, &info.env, &func)?;
                println!("{}", res);
                // TODO multiple values
                for arg in res.args.into_iter() {
                    helper.env.0.insert("_".to_string(), arg);
                }
            }
            Command::Let(id, val) => {
                let v = val.get(&helper.env)?.clone();
                helper.env.0.insert(id.to_string(), v);
            }
            Command::Assert(left, right) => {
                let left = left.get(&helper.env)?;
                let right = right.get(&helper.env)?;
                assert_eq!(left, right);
            }
            Command::Config(conf) => helper.config = Configs::from_dhall(&conf)?,
            Command::Show(val) => {
                let v = val.get(&helper.env)?;
                println!("{}", v);
            }
            Command::Identity(id) => {
                // TODO use existing identity
                use ic_agent::Identity;
                let identity = create_identity()?;
                let sender = identity.sender().map_err(|e| anyhow!("{}", e))?;
                println!("Create identity {}", sender);
                let agent = Agent::builder()
                    .with_url(&helper.agent_url)
                    .with_identity(identity)
                    .build()?;
                {
                    let mut runtime =
                        tokio::runtime::Runtime::new().expect("Unable to create a runtime");
                    runtime.block_on(agent.fetch_root_key())?;
                }
                helper.agent = agent;
                helper
                    .env
                    .0
                    .insert(id.to_string(), IDLValue::Principal(sender));
            }
            Command::Export(file) => {
                use std::io::{BufWriter, Write};
                let file = std::fs::File::create(file)?;
                let mut writer = BufWriter::new(&file);
                let last = helper.history.len() - 1;
                for (i, item) in helper.history.iter().enumerate() {
                    if i < last {
                        let item = item
                            .chars()
                            .map(|c| if c == '\n' { ' ' } else { c })
                            .collect::<String>();
                        writeln!(&mut writer, "{}", item)?;
                    }
                }
            }
        }
        Ok(())
    }
}

impl std::str::FromStr for Command {
    type Err = ParserError;
    fn from_str(str: &str) -> Result<Self, Self::Err> {
        let lexer = Tokenizer::new(str);
        super::grammar::CommandParser::new().parse(lexer)
    }
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

fn create_identity() -> anyhow::Result<impl ic_agent::Identity> {
    let rng = ring::rand::SystemRandom::new();
    let pkcs8_bytes = ring::signature::Ed25519KeyPair::generate_pkcs8(&rng)?
        .as_ref()
        .to_vec();
    Ok(ic_agent::identity::BasicIdentity::from_key_pair(
        ring::signature::Ed25519KeyPair::from_pkcs8(&pkcs8_bytes)?,
    ))
}

// Return position at the end of principal, principal, method, args
pub fn extract_canister(
    line: &str,
    pos: usize,
    env: &NameEnv,
) -> Option<(usize, Principal, String, Vec<Value>)> {
    let command = line[..pos].parse::<Command>().ok()?;
    match command {
        Command::Call {
            canister,
            method,
            args,
        } => {
            let try_id = Principal::from_text(&canister.value);
            let canister_id = match try_id {
                Ok(id) => id,
                Err(_) => env.0.get(&canister.value)?.clone(),
            };
            Some((canister.span.end, canister_id, method, args))
        }
        _ => None,
    }
}
