use super::javascript::compile_ts_js as javascript_compile;
use super::typescript::compile_ts_js as typescript_compile;
use candid::pretty::utils::*;
use candid::types::{Type, TypeEnv};

pub fn compile(env: &TypeEnv, actor: &Option<Type>) -> String {
    let ts = typescript_compile(env, actor);
    let js = javascript_compile(env, actor);

    str(&ts.clone()).append(js).pretty(LINE_WIDTH).to_string()
}
