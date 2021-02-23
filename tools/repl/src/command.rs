use super::helper::MyHelper;
use super::token::{ParserError, Spanned, Tokenizer};
use anyhow::anyhow;
use candid::Principal;
use candid::{
    parser::configs::Configs, parser::value::IDLValue, types::Function, IDLArgs, TypeEnv,
};
use ic_agent::Agent;

#[derive(Debug)]
pub enum Command {
    Call {
        canister: Spanned<Principal>,
        method: String,
        args: Vec<IDLValue>,
    },
    Config(String),
    Show(String),
}

impl Command {
    pub fn run(&self, helper: &mut MyHelper) -> anyhow::Result<()> {
        match self {
            Command::Call {
                canister,
                method,
                args,
            } => {
                let canister_id = &canister.value;
                let agent = &helper.agent;
                let mut map = helper.canister_map.borrow_mut();
                let info = map.get(&agent, canister_id)?;
                let func = info
                    .methods
                    .get(method)
                    .ok_or_else(|| anyhow!("no method {}", method))?;
                let args = IDLArgs {
                    args: args.to_vec(),
                };
                let res = call(&agent, canister_id, &method, &args, &info.env, &func)?;
                println!("{}", res);
            }
            Command::Config(conf) => helper.config = Configs::from_dhall(&conf)?,
            Command::Show(_var) => (),
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
