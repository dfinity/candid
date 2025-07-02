use super::typing::check_prog;
use crate::{Error, Result};
use candid::types::syntax::{Dec, IDLProg, IDLType};
use candid::types::value::IDLArgs;
use candid::types::{Type, TypeEnv};
use candid::DecoderConfig;

const DECODING_COST: usize = 20_000_000;

type TupType = Vec<IDLType>;

pub struct Test {
    pub defs: Vec<Dec>,
    pub asserts: Vec<Assert>,
}

pub struct Assert {
    pub left: Input,
    pub right: Option<Input>,
    pub typ: TupType,
    pub pass: bool,
    pub desc: Option<String>,
}

pub enum Input {
    Text(String),
    Blob(Vec<u8>),
}

/// Generate assertions for host value
pub struct HostTest {
    pub desc: String,
    pub asserts: Vec<HostAssert>,
}
pub enum HostAssert {
    // The encoded bytes is not unique
    Encode(IDLArgs, Vec<Type>, bool, Vec<u8>),
    NotEncode(IDLArgs, Vec<Type>),
    Decode(Vec<u8>, Vec<Type>, bool, IDLArgs),
    NotDecode(Vec<u8>, Vec<Type>),
}

impl Assert {
    pub fn desc(&self) -> String {
        match &self.desc {
            None => "",
            Some(desc) => desc,
        }
        .to_string()
    }
}

impl Input {
    pub fn parse(&self, env: &TypeEnv, types: &[Type]) -> Result<IDLArgs> {
        match self {
            Input::Text(ref s) => Ok(super::parse_idl_args(s)?.annotate_types(true, env, types)?),
            Input::Blob(ref bytes) => {
                let mut config = DecoderConfig::new();
                config.set_decoding_quota(DECODING_COST);
                Ok(IDLArgs::from_bytes_with_types_with_config(
                    bytes, env, types, &config,
                )?)
            }
        }
    }
    fn check_round_trip(&self, v: &IDLArgs, env: &TypeEnv, types: &[Type]) -> Result<bool> {
        match self {
            Input::Blob(ref blob) => {
                let bytes = v.to_bytes_with_types(env, types)?;
                Ok(*blob == bytes)
            }
            Input::Text(_) => Ok(true), //Ok(*s == v.to_string()),
        }
    }
}

impl std::str::FromStr for Test {
    type Err = Error;
    fn from_str(str: &str) -> std::result::Result<Self, Self::Err> {
        let lexer = super::token::Tokenizer::new(str);
        Ok(super::grammar::TestParser::new().parse(None, lexer)?)
    }
}

impl HostTest {
    pub fn from_assert(assert: &Assert, env: &TypeEnv, types: &[Type]) -> Self {
        use HostAssert::*;
        let types = types.to_vec();
        let mut asserts = Vec::new();
        match &assert.left {
            Input::Text(s) => {
                // Without type annotation, numbers are all of type int.
                // Assertion may not pass.
                let parsed = crate::parse_idl_args(s);
                if parsed.is_err() {
                    let desc = format!("(skip) {}", assert.desc());
                    return HostTest { desc, asserts };
                }
                let parsed = parsed.unwrap();
                if !assert.pass && assert.right.is_none() {
                    asserts.push(NotEncode(parsed, types));
                } else {
                    let bytes = parsed.to_bytes_with_types(env, &types).unwrap();
                    asserts.push(Encode(parsed.clone(), types.clone(), true, bytes.clone()));
                    // round tripping
                    let vals = parsed.annotate_types(true, env, &types).unwrap();
                    asserts.push(Decode(bytes, types, true, vals));
                }
                let desc = format!("(encode?) {}", assert.desc());
                HostTest { desc, asserts }
            }
            Input::Blob(bytes) => {
                let bytes = bytes.to_vec();
                if !assert.pass && assert.right.is_none() {
                    asserts.push(NotDecode(bytes, types));
                } else {
                    let mut config = DecoderConfig::new();
                    config.set_decoding_quota(DECODING_COST);
                    let args =
                        IDLArgs::from_bytes_with_types_with_config(&bytes, env, &types, &config)
                            .unwrap();
                    asserts.push(Decode(bytes.clone(), types.clone(), true, args));
                    // round tripping
                    // asserts.push(Encode(args, types.clone(), true, bytes.clone()));
                    if let Some(right) = &assert.right {
                        let expected = right.parse(env, &types).unwrap();
                        if let Input::Blob(blob) = right {
                            asserts.push(Decode(
                                blob.to_vec(),
                                types.clone(),
                                true,
                                expected.clone(),
                            ));
                        }
                        if !assert.pass {
                            asserts.push(Decode(bytes, types, assert.pass, expected));
                        }
                    }
                }
                HostTest {
                    desc: assert.desc(),
                    asserts,
                }
            }
        }
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
        print!("Checking {} {}...", i + 1, assert.desc());
        let mut types = Vec::new();
        for ty in assert.typ.iter() {
            types.push(super::typing::ast_to_type(&env, ty)?);
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
            if assert.pass != is_equal {
                print!(" left:{left}, right:{right} ");
            }
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
