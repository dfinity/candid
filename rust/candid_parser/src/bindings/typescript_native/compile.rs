use super::compile_interface::compile_interface;
use super::compile_wrapper::compile_wrapper;
use crate::syntax::IDLMergedProg;
use candid::types::{Type, TypeEnv};

pub fn compile(
    env: &TypeEnv,
    actor: &Option<Type>,
    service_name: &str,
    target: &str,
    prog: &IDLMergedProg,
) -> String {
    if target == "interface" {
        compile_interface(env, actor, service_name, prog)
    } else if target == "wrapper" {
        compile_wrapper(env, actor, service_name, prog)
    } else {
        panic!("Invalid target: {}", target);
    }
}
