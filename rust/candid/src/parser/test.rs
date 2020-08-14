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
    fn check_round_trip(&self, v: &IDLArgs, env: &TypeEnv, types: &[Type]) -> Result<bool> {
        match self {
            Input::Blob(ref blob) => {
                let bytes = v.to_bytes_with_types(&env, &types)?;
                Ok(*blob == bytes)
            }
            Input::Text(ref s) => Ok(*s == v.to_string()),
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
        print!("Checking {}:{:?}...", i + 1, assert.desc);
        let mut types = Vec::new();
        for ty in assert.typ.iter() {
            types.push(env.ast_to_type(ty)?);
        }
        let input = assert.left.parse(&env, &types);
        let pass = if let Some(assert_right) = &assert.right {
            let left = input?;
            let right = assert_right.parse(&env, &types)?;
            if !assert.left.check_round_trip(&left, &env, &types)?
                || !assert_right.check_round_trip(&right, &env, &types)?
            {
                print!("[round-trip failed] ");
            }
            let is_equal = left == right;
            assert.pass == is_equal
        } else {
            let res = assert.pass == input.is_ok();
            if assert.pass && !assert.left.check_round_trip(&input?, &env, &types)? {
                print!("[round-trip failed] ");
            }
            res
        };
        if pass {
            count += 1;
            println!("[pass]");
        } else {
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
