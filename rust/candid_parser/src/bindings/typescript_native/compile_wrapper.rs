use super::generate_wrapper::TypeConverter;
use super::ident::{contains_unicode_characters, get_ident_guarded, get_ident_guarded_keyword_ok};
use candid::types::{Field, Function, Type, TypeEnv, TypeInner};

use swc_core::common::{SyntaxContext, DUMMY_SP};
use swc_core::ecma::ast::*;

use super::convert_types::convert_type;
use super::generate_wrapper::convert_multi_return_from_candid;

use super::convert_types::add_type_definitions;
use super::preamble::actor::wrapper_canister_initialization;
use super::preamble::imports::{interface_create_actor_options, wrapper_imports};
use super::preamble::options::{interface_options_utils, wrapper_options_utils};
use super::utils::render_ast;

use super::compile_interface::{interface_actor_service, interface_actor_var};
use std::collections::HashMap;

pub fn compile_wrapper(env: &TypeEnv, actor: &Option<Type>, service_name: &str) -> String {
    let enum_declarations: &mut HashMap<Vec<Field>, (TsEnumDecl, String)> = &mut HashMap::new();

    let mut module = Module {
        span: DUMMY_SP,
        body: vec![],
        shebang: None,
    };

    wrapper_imports(&mut module, service_name);

    interface_options_utils(&mut module);

    wrapper_options_utils(&mut module);

    add_type_definitions(enum_declarations, env, &mut module);

    interface_create_actor_options(&mut module);

    if actor.is_some() {
        wrapper_canister_initialization(service_name, &mut module);
    }

    let mut actor_module = Module {
        span: DUMMY_SP,
        body: vec![],
        shebang: None,
    };

    if let Some(actor_type) = actor {
        let mut converter = TypeConverter::new(env, enum_declarations);

        wrapper_actor_implementation(
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

// Add actor implementation
fn wrapper_actor_implementation(
    env: &TypeEnv,
    module: &mut Module,
    actor_type: &Type,
    service_name: &str,
    converter: &mut TypeConverter,
) {
    match actor_type.as_ref() {
        TypeInner::Service(ref serv) => {
            wrapper_actor_service(env, module, serv, service_name, converter)
        }
        TypeInner::Var(id) => wrapper_actor_var(env, module, id, service_name, converter),
        TypeInner::Class(_, t) => {
            wrapper_actor_implementation(env, module, t, service_name, converter)
        }
        _ => {}
    }
}

fn wrapper_actor_service(
    env: &TypeEnv,
    module: &mut Module,
    serv: &[(String, Type)],
    service_name: &str,
    converter: &mut TypeConverter,
) {
    interface_actor_service(env, module, serv, service_name, converter);

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

// Add actor implementation from a type reference
fn wrapper_actor_var(
    env: &TypeEnv,
    module: &mut Module,
    type_id: &str,
    service_name: &str,
    converter: &mut TypeConverter,
) {
    interface_actor_var(module, type_id, service_name);
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

fn create_actor_class(
    env: &TypeEnv,
    service_name: &str,
    capitalized_service_name: &str,
    serv: &[(String, Type)],
    converter: &mut TypeConverter,
) -> ClassDecl {
    // Create private actor field
    let actor_field = ClassMember::ClassProp(ClassProp {
        span: DUMMY_SP,
        key: PropName::Ident(IdentName {
            span: DUMMY_SP,
            sym: "actor".into(),
        }),
        value: None,
        type_ann: Some(Box::new(TsTypeAnn {
            span: DUMMY_SP,
            type_ann: Box::new(TsType::TsTypeRef(TsTypeRef {
                span: DUMMY_SP,
                type_name: TsEntityName::Ident(Ident::new(
                    "ActorSubclass".into(),
                    DUMMY_SP,
                    SyntaxContext::empty(),
                )),
                type_params: Some(Box::new(TsTypeParamInstantiation {
                    span: DUMMY_SP,
                    params: vec![Box::new(TsType::TsTypeRef(TsTypeRef {
                        span: DUMMY_SP,
                        type_name: TsEntityName::Ident(Ident::new(
                            "_SERVICE".into(),
                            DUMMY_SP,
                            SyntaxContext::empty(),
                        )),
                        type_params: None,
                    }))],
                })),
            })),
        })),
        accessibility: Some(Accessibility::Private),
        is_static: false,
        decorators: vec![],
        is_abstract: false,
        declare: false,
        is_optional: false,
        is_override: false,
        readonly: false,
        definite: false,
    });

    // Create constructor
    let constructor = ClassMember::Constructor(Constructor {
        span: DUMMY_SP,
        key: PropName::Ident(
            Ident::new("constructor".into(), DUMMY_SP, SyntaxContext::empty()).into(),
        ),
        params: vec![
            ParamOrTsParamProp::Param(Param {
                span: DUMMY_SP,
                decorators: vec![],
                pat: Pat::Ident(BindingIdent {
                    id: Ident {
                        span: DUMMY_SP,
                        sym: "actor".into(),
                        optional: true,
                        ctxt: SyntaxContext::empty(),
                    },
                    type_ann: Some(Box::new(TsTypeAnn {
                        span: DUMMY_SP,
                        type_ann: Box::new(TsType::TsTypeRef(TsTypeRef {
                            span: DUMMY_SP,
                            type_name: TsEntityName::Ident(Ident::new(
                                "ActorSubclass".into(),
                                DUMMY_SP,
                                SyntaxContext::empty(),
                            )),
                            type_params: Some(Box::new(TsTypeParamInstantiation {
                                span: DUMMY_SP,
                                params: vec![Box::new(TsType::TsTypeRef(TsTypeRef {
                                    span: DUMMY_SP,
                                    type_name: TsEntityName::Ident(Ident::new(
                                        "_SERVICE".into(),
                                        DUMMY_SP,
                                        SyntaxContext::empty(),
                                    )),
                                    type_params: None,
                                }))],
                            })),
                        })),
                    })),
                }),
            }),
            ParamOrTsParamProp::TsParamProp(TsParamProp {
                span: DUMMY_SP,
                decorators: vec![],
                accessibility: Some(Accessibility::Private),
                is_override: false,
                readonly: false,
                param: TsParamPropParam::Ident(BindingIdent {
                    id: Ident {
                        span: DUMMY_SP,
                        sym: "processError".into(),
                        optional: true,
                        ctxt: SyntaxContext::empty(),
                    },
                    type_ann: Some(Box::new(TsTypeAnn {
                        span: DUMMY_SP,
                        type_ann: Box::new(TsType::TsFnOrConstructorType(
                            TsFnOrConstructorType::TsFnType(TsFnType {
                                span: DUMMY_SP,
                                params: vec![TsFnParam::Ident(BindingIdent {
                                    id: Ident::new(
                                        "error".into(),
                                        DUMMY_SP,
                                        SyntaxContext::empty(),
                                    ),
                                    type_ann: Some(Box::new(TsTypeAnn {
                                        span: DUMMY_SP,
                                        type_ann: Box::new(TsType::TsKeywordType(TsKeywordType {
                                            span: DUMMY_SP,
                                            kind: TsKeywordTypeKind::TsUnknownKeyword,
                                        })),
                                    })),
                                })],
                                type_params: None,
                                type_ann: Box::new(TsTypeAnn {
                                    span: DUMMY_SP,
                                    type_ann: Box::new(TsType::TsKeywordType(TsKeywordType {
                                        span: DUMMY_SP,
                                        kind: TsKeywordTypeKind::TsNeverKeyword,
                                    })),
                                }),
                            }),
                        )),
                    })),
                }),
            }),
        ],
        body: Some(BlockStmt {
            span: DUMMY_SP,
            stmts: vec![Stmt::Expr(ExprStmt {
                span: DUMMY_SP,
                expr: Box::new(Expr::Assign(AssignExpr {
                    span: DUMMY_SP,
                    op: AssignOp::Assign,
                    left: AssignTarget::Simple(SimpleAssignTarget::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(Expr::This(ThisExpr { span: DUMMY_SP })),
                        prop: MemberProp::Ident(IdentName {
                            span: DUMMY_SP,
                            sym: "actor".into(),
                        }),
                    })),
                    right: Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::NullishCoalescing,
                        left: Box::new(Expr::Ident(Ident::new(
                            "actor".into(),
                            DUMMY_SP,
                            SyntaxContext::empty(),
                        ))),
                        right: Box::new(Expr::Ident(Ident::new(
                            format!("_{}", service_name).into(),
                            DUMMY_SP,
                            SyntaxContext::empty(),
                        ))),
                    })),
                })),
            })],
            ctxt: SyntaxContext::empty(),
        }),
        accessibility: None,
        is_optional: false,
        ctxt: SyntaxContext::empty(),
    });

    // Create methods for each function in the service
    let methods: Vec<ClassMember> = serv
        .iter()
        .filter_map(|(method_id, func_ty)| {
            if let TypeInner::Func(ref func) = func_ty.as_ref() {
                Some(create_actor_method(env, method_id, func, converter))
            } else if let TypeInner::Var(ref inner_id) = func_ty.as_ref() {
                let inner_id = env.rec_find_type(inner_id).unwrap();
                match inner_id.as_ref() {
                    TypeInner::Func(ref func) => {
                        Some(create_actor_method(env, method_id, func, converter))
                    }
                    _ => None,
                }
            } else {
                None
            }
        })
        .collect();

    // Combine all members
    let mut members = vec![actor_field, constructor];
    members.extend(methods);

    ClassDecl {
        ident: get_ident_guarded(capitalized_service_name),
        declare: false,
        class: Box::new(Class {
            span: DUMMY_SP,
            body: members,
            super_class: None,
            type_params: None,
            super_type_params: None,
            implements: vec![TsExprWithTypeArgs {
                span: DUMMY_SP,
                expr: Box::new(Expr::Ident(get_ident_guarded(&format!(
                    "{}Interface",
                    service_name
                )))),
                type_args: None,
            }],
            is_abstract: false,
            decorators: vec![],
            ctxt: SyntaxContext::empty(),
        }),
    }
}

fn create_actor_method(
    env: &TypeEnv,
    method_id: &str,
    func: &Function,
    converter: &mut TypeConverter,
) -> ClassMember {
    // Create parameters
    let params = func
        .args
        .iter()
        .enumerate()
        .map(|(i, arg_ty)| {
            let var_name = format!("arg{}", i);
            Param {
                span: DUMMY_SP,
                decorators: vec![],
                pat: Pat::Ident(BindingIdent {
                    id: Ident::new(var_name.into(), DUMMY_SP, SyntaxContext::empty()),
                    type_ann: Some(Box::new(TsTypeAnn {
                        span: DUMMY_SP,
                        type_ann: Box::new(convert_type(
                            converter.enum_declarations_mut(),
                            env,
                            &arg_ty.typ,
                            true,
                        )),
                    })),
                }),
            }
        })
        .collect();

    // Create return type
    let return_type = match func.rets.len() {
        0 => TsType::TsKeywordType(TsKeywordType {
            span: DUMMY_SP,
            kind: TsKeywordTypeKind::TsVoidKeyword,
        }),
        1 => convert_type(converter.enum_declarations_mut(), env, &func.rets[0], true),
        _ => {
            // Create a tuple type for multiple return values
            TsType::TsTupleType(TsTupleType {
                span: DUMMY_SP,
                elem_types: func
                    .rets
                    .iter()
                    .map(|ty| TsTupleElement {
                        span: DUMMY_SP,
                        label: None,
                        ty: Box::new(convert_type(
                            converter.enum_declarations_mut(),
                            env,
                            ty,
                            true,
                        )),
                    })
                    .collect(),
            })
        }
    };

    // Wrap return type in Promise
    let promise_return_type = TsTypeRef {
        span: DUMMY_SP,
        type_name: TsEntityName::Ident(Ident::new(
            "Promise".into(),
            DUMMY_SP,
            SyntaxContext::empty(),
        )),
        type_params: Some(Box::new(TsTypeParamInstantiation {
            span: DUMMY_SP,
            params: vec![Box::new(return_type)],
        })),
    };

    // Generate converted arguments for the function call
    let converted_args = func
        .args
        .iter()
        .enumerate()
        .map(|(i, arg_ty)| {
            let var_name = format!("arg{}", i);

            let arg_ident = Ident::new(var_name.into(), DUMMY_SP, SyntaxContext::empty());
            let arg_expr = Expr::Ident(arg_ident);

            // Apply type conversion
            let converted_expr = converter.convert_to_candid(&arg_expr, &arg_ty.typ);

            ExprOrSpread {
                spread: None,
                expr: Box::new(converted_expr),
            }
        })
        .collect::<Vec<_>>();

    let actor_call = if contains_unicode_characters(method_id) {
        Expr::Call(CallExpr {
            span: DUMMY_SP,
            callee: Callee::Expr(Box::new(Expr::Member(MemberExpr {
                span: DUMMY_SP,
                obj: Box::new(Expr::Member(MemberExpr {
                    span: DUMMY_SP,
                    obj: Box::new(Expr::This(ThisExpr { span: DUMMY_SP })),
                    prop: MemberProp::Ident(IdentName {
                        span: DUMMY_SP,
                        sym: "actor".into(),
                    }),
                })),
                prop: MemberProp::Computed(ComputedPropName {
                    span: DUMMY_SP,
                    expr: Box::new(Expr::Lit(Lit::Str(Str {
                        span: DUMMY_SP,
                        value: method_id.into(),
                        raw: None,
                    }))),
                }),
            }))),
            args: converted_args,
            type_args: None,
            ctxt: SyntaxContext::empty(),
        })
    } else {
        // Create the function call to the actor method
        Expr::Call(CallExpr {
            span: DUMMY_SP,
            callee: Callee::Expr(Box::new(Expr::Member(MemberExpr {
                span: DUMMY_SP,
                obj: Box::new(Expr::Member(MemberExpr {
                    span: DUMMY_SP,
                    obj: Box::new(Expr::This(ThisExpr { span: DUMMY_SP })),
                    prop: MemberProp::Ident(IdentName {
                        span: DUMMY_SP,
                        sym: "actor".into(),
                    }),
                })),
                prop: MemberProp::Ident(get_ident_guarded_keyword_ok(method_id).into()),
            }))),
            args: converted_args,
            type_args: None,
            ctxt: SyntaxContext::empty(),
        })
    };

    // Create await expression to call the actor
    let await_expr = Expr::Await(AwaitExpr {
        span: DUMMY_SP,
        arg: Box::new(actor_call),
    });

    // Variable to hold the raw result
    let result_var = Ident::new("result".into(), DUMMY_SP, SyntaxContext::empty());

    // Create the common call and conversion logic
    let call_and_convert_stmts = vec![
        // const result = await actor.method(args);
        Stmt::Decl(Decl::Var(Box::new(VarDecl {
            span: DUMMY_SP,
            kind: VarDeclKind::Const,
            declare: false,
            decls: vec![VarDeclarator {
                span: DUMMY_SP,
                name: Pat::Ident(BindingIdent {
                    id: result_var.clone(),
                    type_ann: None,
                }),
                init: Some(Box::new(await_expr)),
                definite: false,
            }],
            ctxt: SyntaxContext::empty(),
        }))),
        // Return converted result
        Stmt::Return(ReturnStmt {
            span: DUMMY_SP,
            arg: Some(Box::new(if func.rets.is_empty() {
                // No return value
                Expr::Ident(result_var.clone())
            } else {
                // Convert the result to the expected TypeScript type
                let result_expr = Expr::Ident(result_var.clone());
                convert_multi_return_from_candid(converter, &result_expr, &func.rets)
            })),
        }),
    ];

    // Method body with conditional error handling
    let body_stmts = vec![
        // if (this.processError) {
        Stmt::If(IfStmt {
            span: DUMMY_SP,
            test: Box::new(Expr::Member(MemberExpr {
                span: DUMMY_SP,
                obj: Box::new(Expr::This(ThisExpr { span: DUMMY_SP })),
                prop: MemberProp::Ident(
                    Ident::new("processError".into(), DUMMY_SP, SyntaxContext::empty()).into(),
                ),
            })),
            cons: Box::new(Stmt::Block(BlockStmt {
                span: DUMMY_SP,
                stmts: vec![
                    // try {
                    Stmt::Try(Box::new(TryStmt {
                        span: DUMMY_SP,
                        block: BlockStmt {
                            span: DUMMY_SP,
                            stmts: call_and_convert_stmts.clone(),
                            ctxt: SyntaxContext::empty(),
                        },
                        handler: Some(CatchClause {
                            span: DUMMY_SP,
                            param: Some(Pat::Ident(BindingIdent {
                                id: Ident::new("e".into(), DUMMY_SP, SyntaxContext::empty()),
                                type_ann: None,
                            })),
                            body: BlockStmt {
                                span: DUMMY_SP,
                                stmts: vec![
                                    // this.processError(e);
                                    Stmt::Expr(ExprStmt {
                                        span: DUMMY_SP,
                                        expr: Box::new(Expr::Call(CallExpr {
                                            span: DUMMY_SP,
                                            callee: Callee::Expr(Box::new(Expr::Member(
                                                MemberExpr {
                                                    span: DUMMY_SP,
                                                    obj: Box::new(Expr::This(ThisExpr {
                                                        span: DUMMY_SP,
                                                    })),
                                                    prop: MemberProp::Ident(
                                                        Ident::new(
                                                            "processError".into(),
                                                            DUMMY_SP,
                                                            SyntaxContext::empty(),
                                                        )
                                                        .into(),
                                                    ),
                                                },
                                            ))),
                                            args: vec![ExprOrSpread {
                                                spread: None,
                                                expr: Box::new(Expr::Ident(Ident::new(
                                                    "e".into(),
                                                    DUMMY_SP,
                                                    SyntaxContext::empty(),
                                                ))),
                                            }],
                                            type_args: None,
                                            ctxt: SyntaxContext::empty(),
                                        })),
                                    }),
                                    // throw new Error("unreachable");
                                    Stmt::Throw(ThrowStmt {
                                        span: DUMMY_SP,
                                        arg: Box::new(Expr::New(NewExpr {
                                            span: DUMMY_SP,
                                            callee: Box::new(Expr::Ident(Ident::new(
                                                "Error".into(),
                                                DUMMY_SP,
                                                SyntaxContext::empty(),
                                            ))),
                                            args: Some(vec![ExprOrSpread {
                                                spread: None,
                                                expr: Box::new(Expr::Lit(Lit::Str(Str {
                                                    span: DUMMY_SP,
                                                    value: "unreachable".into(),
                                                    raw: None,
                                                }))),
                                            }]),
                                            type_args: None,
                                            ctxt: SyntaxContext::empty(),
                                        })),
                                    }),
                                ],
                                ctxt: SyntaxContext::empty(),
                            },
                        }),
                        finalizer: None,
                    })),
                ],
                ctxt: SyntaxContext::empty(),
            })),
            alt: Some(Box::new(Stmt::Block(BlockStmt {
                span: DUMMY_SP,
                stmts: call_and_convert_stmts,
                ctxt: SyntaxContext::empty(),
            }))),
        }),
    ];

    ClassMember::Method(ClassMethod {
        span: DUMMY_SP,
        key: PropName::Ident(get_ident_guarded(method_id).into()),
        function: Box::new(swc_core::ecma::ast::Function {
            params,
            decorators: vec![],
            span: DUMMY_SP,
            body: Some(BlockStmt {
                span: DUMMY_SP,
                stmts: body_stmts,
                ctxt: SyntaxContext::empty(),
            }),
            is_generator: false,
            is_async: true,
            type_params: None,
            return_type: Some(Box::new(TsTypeAnn {
                span: DUMMY_SP,
                type_ann: Box::new(TsType::TsTypeRef(promise_return_type)),
            })),
            ctxt: SyntaxContext::empty(),
        }),
        kind: MethodKind::Method,
        is_static: false,
        accessibility: None,
        is_abstract: false,
        is_optional: false,
        is_override: false,
    })
}

fn create_actor_instance(service_name: &str, capitalized_service_name: &str) -> ModuleItem {
    ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl {
        span: DUMMY_SP,
        decl: Decl::Var(Box::new(VarDecl {
            span: DUMMY_SP,
            kind: VarDeclKind::Const,
            declare: false,
            decls: vec![VarDeclarator {
                span: DUMMY_SP,
                name: Pat::Ident(BindingIdent {
                    id: get_ident_guarded(service_name),
                    type_ann: Some(Box::new(TsTypeAnn {
                        span: DUMMY_SP,
                        type_ann: Box::new(TsType::TsTypeRef(TsTypeRef {
                            span: DUMMY_SP,
                            type_name: TsEntityName::Ident(get_ident_guarded(&format!(
                                "{}Interface",
                                service_name
                            ))),
                            type_params: None,
                        })),
                    })),
                }),
                init: Some(Box::new(Expr::New(NewExpr {
                    span: DUMMY_SP,
                    callee: Box::new(Expr::Ident(Ident::new(
                        capitalized_service_name.into(),
                        DUMMY_SP,
                        SyntaxContext::empty(),
                    ))),
                    args: Some(vec![]),
                    type_args: None,
                    ctxt: SyntaxContext::empty(),
                }))),
                definite: false,
            }],
            ctxt: SyntaxContext::empty(),
        })),
    }))
}
