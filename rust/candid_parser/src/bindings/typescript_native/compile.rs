use super::generate_wrapper::TypeConverter;
use super::ident::get_ident_guarded;
use super::preamble::actor::{interface_canister_initialization};
use super::preamble::imports::{
    interface_create_actor_options, interface_imports,
};
use super::preamble::options::{interface_options_utils};
use super::utils::render_ast;
use candid::types::{Field, Type, TypeEnv, TypeInner};
use std::collections::HashMap;

use swc_core::common::DUMMY_SP;
use swc_core::ecma::ast::*;

use super::convert_types::{add_type_definitions, create_interface_from_service};
use super::compile_wrapper::compile_wrapper;
use super::compile_interface::compile_interface;

pub fn compile(env: &TypeEnv, actor: &Option<Type>, service_name: &str, target: &str) -> String {
    if target == "interface" {
        compile_interface(env, actor, service_name)
    } else if target == "wrapper" {
        return compile_wrapper(env, actor, service_name);
    } else {
        panic!("Invalid target: {}", target);
    }
}
