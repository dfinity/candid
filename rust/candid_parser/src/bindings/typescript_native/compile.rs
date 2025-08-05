use candid::types::{Type, TypeEnv};

use super::compile_interface::compile_interface;
use super::compile_wrapper::compile_wrapper;

pub fn compile(env: &TypeEnv, actor: &Option<Type>, service_name: &str, target: &str) -> String {
    if target == "interface" {
        compile_interface(env, actor, service_name)
    } else if target == "wrapper" {
        return compile_wrapper(env, actor, service_name);
    } else {
        panic!("Invalid target: {}", target);
    }
}
