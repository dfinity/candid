use super::conversion_functions_generator::TypeConverter;
use super::preamble::actor::interface_canister_initialization;
use super::preamble::imports::{interface_create_actor_options, interface_imports};
use super::preamble::options::interface_options_utils;
use super::utils::get_ident_guarded;
use super::utils::render_ast;
use candid::types::{Field, Type, TypeEnv, TypeInner};
use std::collections::HashMap;

use swc_core::common::DUMMY_SP;
use swc_core::ecma::ast::*;

use super::new_typescript_native_types::{add_type_definitions, create_interface_from_service};

pub fn compile_interface(env: &TypeEnv, actor: &Option<Type>, service_name: &str) -> String {
    let enum_declarations: &mut HashMap<Vec<Field>, (TsEnumDecl, String)> = &mut HashMap::new();

    let mut module = Module {
        span: DUMMY_SP,
        body: vec![],
        shebang: None,
    };

    interface_imports(&mut module);
    interface_options_utils(&mut module);
    add_type_definitions(enum_declarations, env, &mut module);
    interface_create_actor_options(&mut module);
    interface_canister_initialization(service_name, &mut module);

    let mut actor_module = Module {
        span: DUMMY_SP,
        body: vec![],
        shebang: None,
    };

    if let Some(actor_type) = actor {
        let mut converter = TypeConverter::new(env, enum_declarations);

        interface_actor_implementation(
            env,
            &mut actor_module,
            actor_type,
            service_name,
            &mut converter,
        );

        let mut sorted_functions = converter.get_generated_functions();
        sorted_functions.sort_by(|a, b| {
            if let (Stmt::Decl(Decl::Fn(fn_a)), Stmt::Decl(Decl::Fn(fn_b))) = (a, b) {
                fn_a.ident.sym.to_string().cmp(&fn_b.ident.sym.to_string())
            } else {
                std::cmp::Ordering::Equal
            }
        });

        for stmt in sorted_functions {
            actor_module.body.push(ModuleItem::Stmt(stmt.clone()));
        }
    }

    // Add enum declarations to the module, sorted by name for stability
    let mut sorted_enums: Vec<_> = enum_declarations.clone().into_iter().collect();
    sorted_enums.sort_by_key(|(_, (_, enum_name))| enum_name.clone());

    for (_, enum_decl) in sorted_enums {
        module
            .body
            .push(ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl {
                span: DUMMY_SP,
                decl: Decl::TsEnum(Box::new(enum_decl.0)),
            })));
    }

    module.body.extend(actor_module.body);

    // Generate code from the AST
    render_ast(&module)
}

fn interface_actor_implementation(
    env: &TypeEnv,
    module: &mut Module,
    actor_type: &Type,
    service_name: &str,
    converter: &mut TypeConverter,
) {
    match actor_type.as_ref() {
        TypeInner::Service(ref serv) => {
            interface_actor_service(env, module, serv, service_name, converter)
        }
        TypeInner::Var(id) => interface_actor_var(module, id, service_name),
        TypeInner::Class(_, t) => {
            interface_actor_implementation(env, module, t, service_name, converter)
        }
        _ => {}
    }
}

// Add actor implementation from service definition

/// Add actor implementation from service definition
pub fn interface_actor_service(
    env: &TypeEnv,
    module: &mut Module,
    serv: &[(String, Type)],
    service_name: &str,
    converter: &mut TypeConverter,
) {
    let interface =
        create_interface_from_service(converter.enum_declarations_mut(), env, service_name, serv);
    module
        .body
        .push(ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl {
            span: DUMMY_SP,
            decl: Decl::TsInterface(Box::new(interface)),
        })));
}

pub fn interface_actor_var(module: &mut Module, type_id: &str, service_name: &str) {
    let interface = TsInterfaceDecl {
        span: DUMMY_SP,
        declare: false,
        id: get_ident_guarded(&format!("{}Interface", service_name)),
        type_params: None,
        extends: vec![TsExprWithTypeArgs {
            span: DUMMY_SP,
            expr: Box::new(Expr::Ident(get_ident_guarded(&format!(
                "{}Interface",
                type_id
            )))),
            type_args: None,
        }],
        body: TsInterfaceBody {
            span: DUMMY_SP,
            body: vec![],
        },
    };
    module
        .body
        .push(ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl {
            span: DUMMY_SP,
            decl: Decl::TsInterface(Box::new(interface)),
        })));
}
