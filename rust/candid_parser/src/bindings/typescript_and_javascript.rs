use super::javascript::compile as javascript_compile;
use super::typescript::compile as typescript_compile;
use candid::pretty::utils::*;
use candid::types::{Type, TypeEnv};

pub fn compile(env: &TypeEnv, actor: &Option<Type>) -> String {
    let ts = typescript_compile(env, actor, true);
    let js = javascript_compile(env, actor, true);

    str(&ts.clone()).append(js).pretty(LINE_WIDTH).to_string()
}
