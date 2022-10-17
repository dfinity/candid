use candid::{parser::typing::check_str, types::Type, TypeEnv};
use std::{path::PathBuf, str};

use wasm_bindgen::prelude::*;

// When the `wee_alloc` feature is enabled, use `wee_alloc` as the global
// allocator.
#[cfg(feature = "wee_alloc")]
#[global_allocator]
static ALLOC: wee_alloc::WeeAlloc = wee_alloc::WeeAlloc::INIT;

#[wasm_bindgen]
extern "C" {
    fn alert(s: &str);
}

fn check(input: &str) -> (TypeEnv, Option<Type>) {
    let base = PathBuf::new();
    let (env, actor) = check_str(input, true, &base).unwrap();
    (env, actor)
}

#[wasm_bindgen]
pub fn js(input: &str) -> String {
    let (env, actor) = check(input);

    candid::bindings::javascript::compile(&env, &actor)
}

#[wasm_bindgen]
pub fn ts(input: &str) -> String {
    let (env, actor) = check(input);

    candid::bindings::typescript::compile(&env, &actor)
}

#[wasm_bindgen]
pub fn rust(input: &str) -> String {
    let (env, actor) = check(input);

    candid::bindings::rust::compile(&env, &actor)
}
#[wasm_bindgen]
pub fn candid(input: &str) -> String {
    let (env, actor) = check(input);

    candid::bindings::candid::compile(&env, &actor)
}

#[wasm_bindgen]
pub fn motoko(input: &str) -> String {
    let (env, actor) = check(input);

    candid::bindings::motoko::compile(&env, &actor)
}
