use super::generate_wrapper::TypeConverter;
use super::ident::get_ident_guarded;
use super::preamble::actor::{interface_canister_initialization, wrapper_canister_initialization};
use super::preamble::imports::{
    interface_create_actor_options, interface_imports, wrapper_imports,
};
use super::preamble::options::{interface_options_utils, wrapper_options_utils};
use super::utils::render_ast;
use candid::types::{Field, Type, TypeEnv, TypeInner};
use std::collections::HashMap;

use swc_core::common::DUMMY_SP;
use swc_core::ecma::ast::*;

use super::compile_interface::{add_type_definitions, create_interface_from_service};
use super::compile_wrapper::{create_actor_class, create_actor_instance};

pub fn compile(env: &TypeEnv, actor: &Option<Type>, service_name: &str, target: &str) -> String {
    let enum_declarations: &mut HashMap<Vec<Field>, (TsEnumDecl, String)> = &mut HashMap::new();

    let mut module = Module {
        span: DUMMY_SP,
        body: vec![],
        shebang: None,
    };

    if target == "interface" {
        interface_imports(&mut module);
    }
    if target == "wrapper" {
        wrapper_imports(&mut module, service_name);
    }

    interface_options_utils(&mut module);
    if target == "wrapper" {
        wrapper_options_utils(&mut module);
    }

    add_type_definitions(enum_declarations, env, &mut module);

    interface_create_actor_options(&mut module);

    if target == "interface" {
        interface_canister_initialization(service_name, &mut module);
    }

    if target == "wrapper" && actor.is_some() {
        wrapper_canister_initialization(service_name, &mut module);
    }

    let mut actor_module = Module {
        span: DUMMY_SP,
        body: vec![],
        shebang: None,
    };

    if let Some(actor_type) = actor {
        let mut converter = TypeConverter::new(env, enum_declarations);

        add_actor_implementation(
            env,
            &mut actor_module,
            actor_type,
            service_name,
            target,
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

// Add Principal type import

// Add actor implementation
fn add_actor_implementation(
    env: &TypeEnv,
    module: &mut Module,
    actor_type: &Type,
    service_name: &str,
    target: &str,
    converter: &mut TypeConverter,
) {
    match actor_type.as_ref() {
        TypeInner::Service(ref serv) => {
            add_actor_service_implementation(env, module, serv, service_name, target, converter)
        }
        TypeInner::Var(id) => {
            add_actor_var_implementation(env, module, id, service_name, target, converter)
        }
        TypeInner::Class(_, t) => {
            add_actor_implementation(env, module, t, service_name, target, converter)
        }
        _ => {}
    }
}

// Add actor implementation from service definition

/// Add actor implementation from service definition
fn add_actor_service_implementation(
    env: &TypeEnv,
    module: &mut Module,
    serv: &[(String, Type)],
    service_name: &str,
    target: &str,
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

    if target == "wrapper" {
        // Create a single TypeConverter instance
        let capitalized_service_name = service_name
            .chars()
            .next()
            .map_or(String::new(), |c| c.to_uppercase().collect::<String>())
            + &service_name[1..];

        // Pass the converter to create_actor_class
        let class_decl = create_actor_class(
            env,
            service_name,
            &capitalized_service_name,
            serv,
            converter,
        );

        converter.add_candid_type_imports(module, service_name);

        module
            .body
            .push(ModuleItem::Stmt(Stmt::Decl(Decl::Class(class_decl))));

        // Export the instance of the class
        module.body.push(create_actor_instance(
            service_name,
            &capitalized_service_name,
        ));
    }
}

// Add actor implementation from a type reference
fn add_actor_var_implementation(
    env: &TypeEnv,
    module: &mut Module,
    type_id: &str,
    service_name: &str,
    target: &str,
    converter: &mut TypeConverter,
) {
    // Find the service definition
    let type_ref = env.find_type(type_id).unwrap();
    let serv = match type_ref.as_ref() {
        TypeInner::Service(ref serv) => serv,
        TypeInner::Var(var_id) => {
            let referred_type = env.rec_find_type(var_id).unwrap();
            if let TypeInner::Service(ref serv) = referred_type.as_ref() {
                serv
            } else {
                return;
            }
        }
        _ => return,
    };

    // First add the service interface
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
    if target == "wrapper" {
        let capitalized_service_name = service_name
            .chars()
            .next()
            .map_or(String::new(), |c| c.to_uppercase().collect::<String>())
            + &service_name[1..];
        let class_decl = create_actor_class(
            env,
            service_name,
            &capitalized_service_name,
            serv,
            converter,
        );
        converter.add_candid_type_imports(module, service_name);
        module
            .body
            .push(ModuleItem::Stmt(Stmt::Decl(Decl::Class(class_decl))));
        // Export the instance of the class
        module.body.push(create_actor_instance(
            service_name,
            &capitalized_service_name,
        ));
    }
}
