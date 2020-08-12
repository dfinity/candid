use super::types::{Dec, IDLProg, IDLType};
use super::typing::{check_prog, TypeEnv};
use super::value::IDLArgs;
use crate::types::Type;
use crate::{Error, Result};

type TupType = Vec<IDLType>;

pub struct Test {
    pub defs: Vec<Dec>,
    pub asserts: Vec<Assert>,
}

#[derive(Debug)]
pub struct Assert {
    pub left: Input,
    pub right: Option<Input>,
    pub typ: TupType,
    pub pass: bool,
    pub desc: Option<String>,
}

#[derive(Debug)]
pub enum Input {
    Text(String),
    Blob(Vec<u8>),
}

impl Input {
    fn parse(&self, env: &TypeEnv, types: &[Type]) -> Result<IDLArgs> {
        match self {
            Input::Text(ref s) => s.parse::<IDLArgs>()?.annotate_types(env, types),
            Input::Blob(ref bytes) => Ok(IDLArgs::from_bytes_with_types(bytes, env, types)?),
        }
    }
}

impl std::str::FromStr for Test {
    type Err = Error;
    fn from_str(str: &str) -> std::result::Result<Self, Self::Err> {
        let lexer = super::lexer::Lexer::new(str);
        Ok(super::grammar::TestParser::new().parse(lexer)?)
    }
}

pub fn check(test: Test) -> Result<()> {
    let mut env = TypeEnv::new();
    let prog = IDLProg {
        decs: test.defs,
        actor: None,
    };
    check_prog(&mut env, &prog)?;
    let mut count = 0;
    for (i, assert) in test.asserts.iter().enumerate() {
        print!("Checking {}:{:?}\t\t", i, assert.desc);
        let mut types = Vec::new();
        for ty in assert.typ.iter() {
            types.push(env.ast_to_type(ty)?);
        }
        let input = assert.left.parse(&env, &types);
        let pass = if assert.pass {
            input.is_ok()
        } else {
            input.is_err()
        };
        if pass {
            count += 1;
            println!("[pass]");
        } else {
            /*if let Input::Blob(s) = &assert.left {
                println!("{}", hex::encode(s))
            }*/
            println!("[fail]");
        }
    }
    if count == test.asserts.len() {
        Ok(())
    } else {
        Err(Error::msg(format!(
            "{}/{} passed",
            count,
            test.asserts.len()
        )))
    }
}
