use super::conversion_functions_generator::TypeConverter;
use super::new_typescript_native_types::{add_type_definitions, create_interface_from_service};
use super::preamble::actor::interface_canister_initialization;
use super::preamble::imports::{interface_imports};
use super::preamble::options::interface_options_utils;
use super::utils::get_ident_guarded;
use super::utils::render_ast;
use super::utils::EnumDeclarations;
use crate::bindings::typescript_native::comments::add_comments;
use crate::syntax::{IDLMergedProg, IDLType};
use candid::types::{Type, TypeEnv, TypeInner};
use std::collections::HashMap;
use swc_core::common::Span;
use swc_core::common::DUMMY_SP;
use swc_core::ecma::ast::*;

pub fn compile_interface(
    env: &TypeEnv,
    actor: &Option<Type>,
    service_name: &str,
    prog: &IDLMergedProg,
) -> String {
    let enum_declarations: &mut EnumDeclarations = &mut HashMap::new();

    let mut module = Module {
        span: DUMMY_SP,
        body: vec![],
        shebang: None,
    };

    interface_imports(&mut module, service_name);
    interface_options_utils(&mut module);
    let mut comments = swc_core::common::comments::SingleThreadedComments::default();
    let mut cursor = super::comments::PosCursor::new();
    add_type_definitions(
        enum_declarations,
        &mut comments,
        &mut cursor,
        env,
        &mut module,
        prog,
    );
    interface_canister_initialization(service_name, &mut module);

    let mut actor_module = Module {
        span: DUMMY_SP,
        body: vec![],
        shebang: None,
    };

    if let Some(actor_type) = actor {
        let syntax_actor = prog.resolve_actor().ok().flatten();
        let span = syntax_actor
            .as_ref()
            .map(|s| add_comments(&mut comments, &mut cursor, s.docs.as_ref()))
            .unwrap_or(DUMMY_SP);
        let mut converter = TypeConverter::new(env, enum_declarations, &mut comments, &mut cursor);
        interface_actor_implementation(
            env,
            &mut actor_module,
            actor_type,
            syntax_actor.as_ref().map(|s| &s.typ),
            service_name,
            &mut converter,
            span,
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
    render_ast(&module, &comments)
}

fn interface_actor_implementation(
    env: &TypeEnv,
    module: &mut Module,
    actor_type: &Type,
    syntax: Option<&IDLType>,
    service_name: &str,
    converter: &mut TypeConverter,
    span: Span,
) {
    match actor_type.as_ref() {
        TypeInner::Service(ref serv) => {
            interface_actor_service(env, syntax, module, serv, service_name, converter, span)
        }
        TypeInner::Var(id) => interface_actor_var(module, id.as_str(), service_name, span),
        TypeInner::Class(_, t) => {
            if let Some(IDLType::ClassT(_, syntax_t)) = syntax {
                interface_actor_implementation(
                    env,
                    module,
                    t,
                    Some(syntax_t),
                    service_name,
                    converter,
                    span,
                )
            } else {
                interface_actor_implementation(env, module, t, None, service_name, converter, span)
            }
        }
        _ => {}
    }
}

// Add actor implementation from service definition

/// Add actor implementation from service definition
pub fn interface_actor_service(
    env: &TypeEnv,
    syntax: Option<&IDLType>,
    module: &mut Module,
    serv: &[(String, Type)],
    service_name: &str,
    converter: &mut TypeConverter,
    span: Span,
) {
    let (enum_declarations, comments, cursor) = converter.conv_mut();
    let interface = create_interface_from_service(
        enum_declarations,
        comments,
        cursor,
        env,
        service_name,
        syntax,
        serv,
    );
    module
        .body
        .push(ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl {
            span,
            decl: Decl::TsInterface(Box::new(interface)),
        })));
}

pub fn interface_actor_var(module: &mut Module, type_id: &str, service_name: &str, span: Span) {
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
            span,
            decl: Decl::TsInterface(Box::new(interface)),
        })));
}
