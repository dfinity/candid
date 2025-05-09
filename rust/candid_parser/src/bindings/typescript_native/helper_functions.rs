use swc_core::common::{SyntaxContext, DUMMY_SP};
use swc_core::ecma::ast::*;
use swc_core::ecma::ast::{AssignTarget, SimpleAssignTarget};

use super::ident::get_ident_guarded;

// Add Option helper types
pub fn add_option_helpers_interface(module: &mut Module) {
    let some_type = create_some_type();
    module
        .body
        .push(ModuleItem::Stmt(Stmt::Decl(Decl::TsInterface(Box::new(
            some_type,
        )))));

    let none_type = create_none_type();
    module
        .body
        .push(ModuleItem::Stmt(Stmt::Decl(Decl::TsInterface(Box::new(
            none_type,
        )))));

    let option_type = create_option_type();
    module
        .body
        .push(ModuleItem::Stmt(Stmt::Decl(Decl::TsTypeAlias(Box::new(
            option_type,
        )))));
}
pub fn add_option_helpers_wrapper(module: &mut Module) {
    let some_function = create_some_function();
    module
        .body
        .push(ModuleItem::Stmt(Stmt::Decl(Decl::Fn(some_function))));

    // none() helper function
    let none_function = create_none_function();
    module
        .body
        .push(ModuleItem::Stmt(Stmt::Decl(Decl::Fn(none_function))));

    let is_none_function = create_is_none_function();
    module
        .body
        .push(ModuleItem::Stmt(Stmt::Decl(Decl::Fn(is_none_function))));

    let is_some_function = create_is_some_function();
    module
        .body
        .push(ModuleItem::Stmt(Stmt::Decl(Decl::Fn(is_some_function))));

    let unwrap_function = generate_unwrap_function();
    module
        .body
        .push(ModuleItem::Stmt(Stmt::Decl(Decl::Fn(unwrap_function))));

    let candid_some_function = generate_candid_some_function();
    module
        .body
        .push(ModuleItem::Stmt(Stmt::Decl(Decl::Fn(candid_some_function))));
    let candid_none_function = generate_candid_none_function();
    module
        .body
        .push(ModuleItem::Stmt(Stmt::Decl(Decl::Fn(candid_none_function))));

    let opt_struct_function = generate_record_opt_undefined();
    module
        .body
        .push(ModuleItem::Stmt(Stmt::Decl(Decl::Fn(opt_struct_function))));

    // Add error message parser
    let extract_agent_error_message = generate_extract_agent_error_function();
    module.body.push(ModuleItem::Stmt(Stmt::Decl(Decl::Fn(
        extract_agent_error_message,
    ))));
}

pub fn add_create_actor_imports_and_interface(module: &mut Module) {
    // Add import declaration for types from "@dfinity/agent"
    let import_decl = generate_agent_imports();
    module
        .body
        .push(ModuleItem::ModuleDecl(ModuleDecl::Import(import_decl)));

    let create_actor_options_interface = generate_create_actor_options_interface();
    module
        .body
        .push(ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl {
            span: DUMMY_SP,
            decl: Decl::TsInterface(create_actor_options_interface),
        })));

    // Add CreateActorOptions interface declaration
}

fn generate_create_actor_options_interface() -> Box<TsInterfaceDecl> {
    Box::new(TsInterfaceDecl {
        span: DUMMY_SP,
        id: Ident::new(
            "CreateActorOptions".into(),
            DUMMY_SP,
            SyntaxContext::empty(),
        ),
        declare: true,
        extends: vec![],
        type_params: None,
        body: TsInterfaceBody {
            span: DUMMY_SP,
            body: vec![
                // agent?: Agent
                TsTypeElement::TsPropertySignature(TsPropertySignature {
                    span: DUMMY_SP,
                    readonly: false,
                    key: Box::new(Expr::Ident(Ident::new(
                        "agent".into(),
                        DUMMY_SP,
                        SyntaxContext::empty(),
                    ))),
                    computed: false,
                    optional: true,
                    type_ann: Some(Box::new(TsTypeAnn {
                        span: DUMMY_SP,
                        type_ann: Box::new(TsType::TsTypeRef(TsTypeRef {
                            span: DUMMY_SP,
                            type_name: TsEntityName::Ident(Ident::new(
                                "Agent".into(),
                                DUMMY_SP,
                                SyntaxContext::empty(),
                            )),
                            type_params: None,
                        })),
                    })),
                }),
                // agentOptions?: HttpAgentOptions
                TsTypeElement::TsPropertySignature(TsPropertySignature {
                    span: DUMMY_SP,
                    readonly: false,
                    key: Box::new(Expr::Ident(Ident::new(
                        "agentOptions".into(),
                        DUMMY_SP,
                        SyntaxContext::empty(),
                    ))),
                    computed: false,
                    optional: true,

                    type_ann: Some(Box::new(TsTypeAnn {
                        span: DUMMY_SP,
                        type_ann: Box::new(TsType::TsTypeRef(TsTypeRef {
                            span: DUMMY_SP,
                            type_name: TsEntityName::Ident(Ident::new(
                                "HttpAgentOptions".into(),
                                DUMMY_SP,
                                SyntaxContext::empty(),
                            )),
                            type_params: None,
                        })),
                    })),
                }),
                // actorOptions?: ActorConfig
                TsTypeElement::TsPropertySignature(TsPropertySignature {
                    span: DUMMY_SP,
                    readonly: false,
                    key: Box::new(Expr::Ident(Ident::new(
                        "actorOptions".into(),
                        DUMMY_SP,
                        SyntaxContext::empty(),
                    ))),
                    computed: false,
                    optional: true,
                    type_ann: Some(Box::new(TsTypeAnn {
                        span: DUMMY_SP,
                        type_ann: Box::new(TsType::TsTypeRef(TsTypeRef {
                            span: DUMMY_SP,
                            type_name: TsEntityName::Ident(Ident::new(
                                "ActorConfig".into(),
                                DUMMY_SP,
                                SyntaxContext::empty(),
                            )),
                            type_params: None,
                        })),
                    })),
                }),
            ],
        },
    })
}

fn generate_agent_imports() -> ImportDecl {
    ImportDecl {
        span: DUMMY_SP,
        specifiers: vec![
            ImportSpecifier::Named(ImportNamedSpecifier {
                span: DUMMY_SP,
                local: Ident::new("ActorCallError".into(), DUMMY_SP, SyntaxContext::empty()),
                imported: None,
                is_type_only: false,
            }),
            ImportSpecifier::Named(ImportNamedSpecifier {
                span: DUMMY_SP,
                local: Ident::new("HttpAgentOptions".into(), DUMMY_SP, SyntaxContext::empty()),
                imported: None,
                is_type_only: true,
            }),
            ImportSpecifier::Named(ImportNamedSpecifier {
                span: DUMMY_SP,
                local: Ident::new("ActorConfig".into(), DUMMY_SP, SyntaxContext::empty()),
                imported: None,
                is_type_only: true,
            }),
            ImportSpecifier::Named(ImportNamedSpecifier {
                span: DUMMY_SP,
                local: Ident::new("Agent".into(), DUMMY_SP, SyntaxContext::empty()),
                imported: None,
                is_type_only: true,
            }),
        ],
        src: Box::new(Str {
            span: DUMMY_SP,
            value: "@dfinity/agent".into(),
            raw: None,
        }),
        type_only: false,
        with: None,
        phase: Default::default(),
    }
}

pub fn generate_create_actor_function(service_name: &str) -> FnDecl {
    let capitalized_service_name = service_name
        .chars()
        .next()
        .map_or(String::new(), |c| c.to_uppercase().collect::<String>())
        + &service_name[1..];
    FnDecl {
        ident: Ident::new("createActor".into(), DUMMY_SP, SyntaxContext::empty()),
        declare: false,
        function: Box::new(Function {
            params: vec![
                // canisterId: string | Principal
                Param {
                    span: DUMMY_SP,
                    decorators: vec![],
                    pat: Pat::Ident(BindingIdent {
                        id: Ident::new("canisterId".into(), DUMMY_SP, SyntaxContext::empty()),
                        type_ann: Some(Box::new(TsTypeAnn {
                            span: DUMMY_SP,
                            type_ann: Box::new(TsType::TsUnionOrIntersectionType(
                                TsUnionOrIntersectionType::TsUnionType(TsUnionType {
                                    span: DUMMY_SP,
                                    types: vec![
                                        Box::new(TsType::TsKeywordType(TsKeywordType {
                                            span: DUMMY_SP,
                                            kind: TsKeywordTypeKind::TsStringKeyword,
                                        })),
                                        Box::new(TsType::TsTypeRef(TsTypeRef {
                                            span: DUMMY_SP,
                                            type_name: TsEntityName::Ident(Ident::new(
                                                "Principal".into(),
                                                DUMMY_SP,
                                                SyntaxContext::empty(),
                                            )),
                                            type_params: None,
                                        })),
                                    ],
                                }),
                            )),
                        })),
                    }),
                },
                // options: CreateActorOptions
                Param {
                    span: DUMMY_SP,
                    decorators: vec![],
                    pat: Pat::Ident(BindingIdent {
                        id: Ident {
                            span: DUMMY_SP,
                            sym: "options".into(),
                            optional: true,
                            ctxt: SyntaxContext::empty(),
                        },
                        type_ann: Some(Box::new(TsTypeAnn {
                            span: DUMMY_SP,
                            type_ann: Box::new(TsType::TsTypeRef(TsTypeRef {
                                span: DUMMY_SP,
                                type_name: TsEntityName::Ident(Ident::new(
                                    "CreateActorOptions".into(),
                                    DUMMY_SP,
                                    SyntaxContext::empty(),
                                )),
                                type_params: None,
                            })),
                        })),
                    }),
                },
            ],
            decorators: vec![],
            span: DUMMY_SP,
            body: Some(BlockStmt {
                span: DUMMY_SP,
                stmts: vec![
                    // if (!options) { options = {}; }
                    Stmt::If(IfStmt {
                        span: DUMMY_SP,
                        test: Box::new(Expr::Unary(UnaryExpr {
                            span: DUMMY_SP,
                            op: UnaryOp::Bang,
                            arg: Box::new(Expr::Ident(Ident::new(
                                "options".into(),
                                DUMMY_SP,
                                SyntaxContext::empty(),
                            ))),
                        })),
                        cons: Box::new(Stmt::Block(BlockStmt {
                            span: DUMMY_SP,
                            stmts: vec![Stmt::Expr(ExprStmt {
                                span: DUMMY_SP,
                                expr: Box::new(Expr::Assign(AssignExpr {
                                    span: DUMMY_SP,
                                    op: AssignOp::Assign,
                                    left: AssignTarget::Simple(SimpleAssignTarget::Ident(Ident::new(
                                        "options".into(),
                                        DUMMY_SP,
                                        SyntaxContext::empty(),
                                    ).into() )),
                                    right: Box::new(Expr::Object(ObjectLit {
                                        span: DUMMY_SP,
                                        props: vec![],
                                    })),
                                })),
                            })],
                            ctxt: SyntaxContext::empty(),
                        })),
                        alt: None,
                    }),
                    // if (process.env.BACKEND_HOST) { ... }
                    Stmt::If(IfStmt {
                        span: DUMMY_SP,
                        test: Box::new(Expr::Member(MemberExpr {
                            span: DUMMY_SP,
                            obj: Box::new(Expr::Member(MemberExpr {
                                span: DUMMY_SP,
                                obj: Box::new(Expr::Ident(Ident::new(
                                    "process".into(),
                                    DUMMY_SP,
                                    SyntaxContext::empty(),
                                ).into())),
                                prop: MemberProp::Ident(Ident::new(
                                    "env".into(),
                                    DUMMY_SP,
                                    SyntaxContext::empty(),
                                ).into()),
                            })),
                            prop: MemberProp::Ident(Ident::new(
                                "BACKEND_HOST".into(),
                                DUMMY_SP,
                                SyntaxContext::empty(),
                            ).into()),
                        })),
                        cons: Box::new(Stmt::Block(BlockStmt {
                            span: DUMMY_SP,
                            stmts: vec![Stmt::Expr(ExprStmt {
                                span: DUMMY_SP,
                                expr: Box::new(Expr::Assign(AssignExpr {
                                    span: DUMMY_SP,
                                    op: AssignOp::Assign,
                                    left: AssignTarget::Simple(SimpleAssignTarget::Ident(Ident::new(
                                        "options".into(),
                                        DUMMY_SP,
                                        SyntaxContext::empty(),
                                    ).into() )),
                                    right: Box::new(Expr::Object(ObjectLit {
                                        span: DUMMY_SP,
                                        props: vec![
                                            PropOrSpread::Spread(SpreadElement {
                                                dot3_token: DUMMY_SP,
                                                expr: Box::new(Expr::Ident(Ident::new(
                                                    "options".into(),
                                                    DUMMY_SP,
                                                    SyntaxContext::empty(),
                                                ))),
                                            }),
                                            PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                                                key: PropName::Ident(Ident::new(
                                                    "agentOptions".into(),
                                                    DUMMY_SP,
                                                    SyntaxContext::empty(),
                                                ).into()),
                                                value: Box::new(Expr::Object(ObjectLit {
                                                    span: DUMMY_SP,
                                                    props: vec![
                                                        PropOrSpread::Spread(SpreadElement {
                                                            dot3_token: DUMMY_SP,
                                                            expr: Box::new(Expr::Member(MemberExpr {
                                                                span: DUMMY_SP,
                                                                obj: Box::new(Expr::Ident(
                                                                    Ident::new(
                                                                        "options".into(),
                                                                        DUMMY_SP,
                                                                        SyntaxContext::empty(),
                                                                    ).into(),
                                                                )),
                                                                prop: MemberProp::Ident(Ident::new(
                                                                    "agentOptions".into(),
                                                                    DUMMY_SP,
                                                                    SyntaxContext::empty(),
                                                                ).into() ),
                                                            })),
                                                        }),
                                                        PropOrSpread::Prop(Box::new(
                                                            Prop::KeyValue(KeyValueProp {
                                                                key: PropName::Ident(Ident::new(
                                                                    "host".into(),
                                                                    DUMMY_SP,
                                                                    SyntaxContext::empty(),
                                                                ).into()),
                                                                value: Box::new(Expr::Member(
                                                                    MemberExpr {
                                                                        span: DUMMY_SP,
                                                                        obj: Box::new(
                                                                            Expr::Member(MemberExpr {
                                                                                span: DUMMY_SP,
                                                                                obj: Box::new(
                                                                                    Expr::Ident(
                                                                                        Ident::new(
                                                                                            "process"
                                                                                                .into(),
                                                                                            DUMMY_SP,
                                                                                            SyntaxContext::empty(),
                                                                                        ),
                                                                                    ),
                                                                                ),
                                                                                prop: MemberProp::Ident(
                                                                                    Ident::new(
                                                                                        "env".into(),
                                                                                        DUMMY_SP,
                                                                                        SyntaxContext::empty(),
                                                                                    ).into(),
                                                                                ),
                                                                            }),
                                                                        ),
                                                                        prop: MemberProp::Ident(
                                                                            Ident::new(
                                                                                "BACKEND_HOST"
                                                                                    .into(),
                                                                                DUMMY_SP,
                                                                                SyntaxContext::empty(),
                                                                            ).into(),
                                                                        ),
                                                                    },
                                                                )),
                                                            }),
                                                        )),
                                                    ],
                                                })),
                                            }))),
                                        ],
                                    })),
                                })),
                            })],
                            ctxt: SyntaxContext::empty(),
                        })),
                        alt: None,
                    }),
                    // const actor = _createActor(canisterId, options);
                    Stmt::Decl(Decl::Var(Box::new(VarDecl {
                        ctxt: SyntaxContext::empty(),
                        span: DUMMY_SP,
                        kind: VarDeclKind::Const,
                        declare: false,
                        decls: vec![VarDeclarator {
                            span: DUMMY_SP,
                            name: Pat::Ident(BindingIdent {
                                id: Ident::new("actor".into(), DUMMY_SP, SyntaxContext::empty()),
                                type_ann: None,
                            }),
                            init: Some(Box::new(Expr::Call(CallExpr {
                                span: DUMMY_SP,
                                callee: Callee::Expr(Box::new(Expr::Ident(Ident::new(
                                    "_createActor".into(),
                                    DUMMY_SP,
                                    SyntaxContext::empty(),
                                )))),
                                args: vec![
                                    ExprOrSpread {
                                        spread: None,
                                        expr: Box::new(Expr::Ident(Ident::new(
                                            "canisterId".into(),
                                            DUMMY_SP,
                                            SyntaxContext::empty(),
                                        ))),
                                    },
                                    ExprOrSpread {
                                        spread: None,
                                        expr: Box::new(Expr::Ident(Ident::new(
                                            "options".into(),
                                            DUMMY_SP,
                                            SyntaxContext::empty(),
                                        ))),
                                    },
                                ],
                                type_args: None,
                                ctxt: SyntaxContext::empty(),
                            }))),
                            definite: false,
                        }],
                    }))),
                    // return new Backend(actor);
                    Stmt::Return(ReturnStmt {
                        span: DUMMY_SP,
                        arg: Some(Box::new(Expr::New(NewExpr {
                            span: DUMMY_SP,
                            callee: Box::new(Expr::Ident(Ident::new(
                                capitalized_service_name.into(),
                                DUMMY_SP,
                                SyntaxContext::empty(),
                            ))),
                            args: Some(vec![ExprOrSpread {
                                spread: None,
                                expr: Box::new(Expr::Ident(Ident::new(
                                    "actor".into(),
                                    DUMMY_SP,
                                    SyntaxContext::empty(),
                                ))),
                            }]),
                            type_args: None,
                            ctxt: SyntaxContext::empty(),
                        }))),
                    }),
                ],
                ctxt: SyntaxContext::empty(),
            }),
            is_generator: false,
            is_async: false,
            type_params: None,
            return_type: Some(Box::new(TsTypeAnn {
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
            ctxt: SyntaxContext::empty(),
        }),
    }
}

pub fn create_canister_id_declaration() -> ModuleItem {
    ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl {
        span: DUMMY_SP,
        decl: Decl::Var(Box::new(VarDecl {
            span: DUMMY_SP,
            ctxt: SyntaxContext::empty(),
            kind: VarDeclKind::Const,
            declare: true,
            decls: vec![VarDeclarator {
                span: DUMMY_SP,
                name: Pat::Ident(BindingIdent {
                    id: Ident::new("canisterId".into(), DUMMY_SP, SyntaxContext::empty()),
                    type_ann: Some(Box::new(TsTypeAnn {
                        span: DUMMY_SP,
                        type_ann: Box::new(TsType::TsKeywordType(TsKeywordType {
                            span: DUMMY_SP,
                            kind: TsKeywordTypeKind::TsStringKeyword,
                        })),
                    })),
                }),
                init: None,
                definite: false,
            }],
        })),
    }))
}

pub fn create_canister_id_assignment() -> ModuleItem {
    ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl {
        span: DUMMY_SP,
        decl: Decl::Var(Box::new(VarDecl {
            span: DUMMY_SP,
            ctxt: SyntaxContext::empty(),
            kind: VarDeclKind::Const,
            declare: false,
            decls: vec![VarDeclarator {
                span: DUMMY_SP,
                name: Pat::Ident(BindingIdent {
                    id: Ident::new("canisterId".into(), DUMMY_SP, SyntaxContext::empty()),
                    type_ann: None,
                }),
                init: Some(Box::new(Expr::Ident(Ident::new(
                    "_canisterId".into(),
                    DUMMY_SP,
                    SyntaxContext::empty(),
                )))),
                definite: false,
            }],
        })),
    }))
}

pub fn generate_create_actor_function_declaration(service_name: &str) -> VarDecl {
    VarDecl {
        ctxt: SyntaxContext::empty(),
        span: DUMMY_SP,
        kind: VarDeclKind::Const,
        declare: true,
        decls: vec![VarDeclarator {
            span: DUMMY_SP,
            name: Pat::Ident(BindingIdent {
                id: Ident::new("createActor".into(), DUMMY_SP, SyntaxContext::empty()),
                type_ann: Some(Box::new(TsTypeAnn {
                    span: DUMMY_SP,
                    type_ann: Box::new(TsType::TsFnOrConstructorType(
                        TsFnOrConstructorType::TsFnType(TsFnType {
                            span: DUMMY_SP,
                            params: vec![
                                // First parameter: canisterId: string | Principal
                                TsFnParam::Ident(BindingIdent {
                                    id: Ident::new(
                                        "canisterId".into(),
                                        DUMMY_SP,
                                        SyntaxContext::empty(),
                                    ),
                                    type_ann: Some(Box::new(TsTypeAnn {
                                        span: DUMMY_SP,
                                        type_ann: Box::new(TsType::TsUnionOrIntersectionType(
                                            TsUnionOrIntersectionType::TsUnionType(TsUnionType {
                                                span: DUMMY_SP,
                                                types: vec![
                                                    Box::new(TsType::TsKeywordType(
                                                        TsKeywordType {
                                                            span: DUMMY_SP,
                                                            kind:
                                                                TsKeywordTypeKind::TsStringKeyword,
                                                        },
                                                    )),
                                                    Box::new(TsType::TsTypeRef(TsTypeRef {
                                                        span: DUMMY_SP,
                                                        type_name: TsEntityName::Ident(Ident::new(
                                                            "Principal".into(),
                                                            DUMMY_SP,
                                                            SyntaxContext::empty(),
                                                        )),
                                                        type_params: None,
                                                    })),
                                                ],
                                            }),
                                        )),
                                    })),
                                }),
                                // Second parameter: options?: CreateActorOptions
                                TsFnParam::Ident(BindingIdent {
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
                                                "CreateActorOptions".into(),
                                                DUMMY_SP,
                                                SyntaxContext::empty(),
                                            )),
                                            type_params: None,
                                        })),
                                    })),
                                }),
                            ],
                            type_params: None,
                            type_ann: Box::new(TsTypeAnn {
                                span: DUMMY_SP,
                                type_ann: Box::new(TsType::TsTypeRef(TsTypeRef {
                                    span: DUMMY_SP,
                                    type_name: TsEntityName::Ident(get_ident_guarded(service_name)),
                                    type_params: None,
                                })),
                            }),
                        }),
                    )),
                })),
            }),
            init: None,
            definite: false,
        }],
    }
}

fn generate_record_opt_undefined() -> FnDecl {
    FnDecl {
        ident: Ident::new(
            "record_opt_to_undefined".into(),
            DUMMY_SP,
            SyntaxContext::empty(),
        ),
        declare: false,
        function: Box::new(swc_core::ecma::ast::Function {
            ctxt: SyntaxContext::empty(),
            params: vec![Param {
                span: DUMMY_SP,
                decorators: vec![],
                pat: Pat::Ident(BindingIdent {
                    id: Ident::new("arg".into(), DUMMY_SP, SyntaxContext::empty()),
                    type_ann: Some(Box::new(TsTypeAnn {
                        span: DUMMY_SP,
                        type_ann: Box::new(TsType::TsUnionOrIntersectionType(
                            TsUnionOrIntersectionType::TsUnionType(TsUnionType {
                                span: DUMMY_SP,
                                types: vec![
                                    Box::new(TsType::TsTypeRef(TsTypeRef {
                                        span: DUMMY_SP,
                                        type_name: TsEntityName::Ident(Ident::new(
                                            "T".into(),
                                            DUMMY_SP,
                                            SyntaxContext::empty(),
                                        )),
                                        type_params: None,
                                    })),
                                    Box::new(TsType::TsKeywordType(TsKeywordType {
                                        span: DUMMY_SP,
                                        kind: TsKeywordTypeKind::TsNullKeyword,
                                    })),
                                ],
                            }),
                        )),
                    })),
                }),
            }],
            decorators: vec![],
            span: DUMMY_SP,
            body: Some(BlockStmt {
                span: DUMMY_SP,
                stmts: vec![Stmt::Return(ReturnStmt {
                    span: DUMMY_SP,
                    arg: Some(Box::new(Expr::Cond(CondExpr {
                        span: DUMMY_SP,
                        test: Box::new(Expr::Bin(BinExpr {
                            span: DUMMY_SP,
                            op: BinaryOp::EqEq,
                            left: Box::new(Expr::Ident(Ident::new(
                                "arg".into(),
                                DUMMY_SP,
                                SyntaxContext::empty(),
                            ))),
                            right: Box::new(Expr::Lit(Lit::Null(Null { span: DUMMY_SP }))),
                        })),
                        cons: Box::new(Expr::Ident(Ident::new(
                            "undefined".into(),
                            DUMMY_SP,
                            SyntaxContext::empty(),
                        ))),
                        alt: Box::new(Expr::Ident(Ident::new(
                            "arg".into(),
                            DUMMY_SP,
                            SyntaxContext::empty(),
                        ))),
                    }))),
                })],
                ctxt: SyntaxContext::empty(),
            }),
            is_generator: false,
            is_async: false,
            type_params: Some(Box::new(TsTypeParamDecl {
                span: DUMMY_SP,
                params: vec![TsTypeParam {
                    span: DUMMY_SP,
                    name: Ident::new("T".into(), DUMMY_SP, SyntaxContext::empty()),
                    constraint: None,
                    default: None,
                    is_in: false,
                    is_out: false,
                    is_const: false,
                }],
            })),
            return_type: Some(Box::new(TsTypeAnn {
                span: DUMMY_SP,
                type_ann: Box::new(TsType::TsUnionOrIntersectionType(
                    TsUnionOrIntersectionType::TsUnionType(TsUnionType {
                        span: DUMMY_SP,
                        types: vec![
                            Box::new(TsType::TsTypeRef(TsTypeRef {
                                span: DUMMY_SP,
                                type_name: TsEntityName::Ident(Ident::new(
                                    "T".into(),
                                    DUMMY_SP,
                                    SyntaxContext::empty(),
                                )),
                                type_params: None,
                            })),
                            Box::new(TsType::TsKeywordType(TsKeywordType {
                                span: DUMMY_SP,
                                kind: TsKeywordTypeKind::TsUndefinedKeyword,
                            })),
                        ],
                    }),
                )),
            })),
        }),
    }
}

fn generate_unwrap_function() -> FnDecl {
    FnDecl {
        ident: Ident::new("unwrap".into(), DUMMY_SP, SyntaxContext::empty()),
        declare: false,
        function: Box::new(swc_core::ecma::ast::Function {
            ctxt: SyntaxContext::empty(),
            params: vec![Param {
                span: DUMMY_SP,
                decorators: vec![],
                pat: Pat::Ident(BindingIdent {
                    id: Ident::new("option".into(), DUMMY_SP, SyntaxContext::empty()),
                    type_ann: Some(Box::new(TsTypeAnn {
                        span: DUMMY_SP,
                        type_ann: Box::new(TsType::TsTypeRef(TsTypeRef {
                            span: DUMMY_SP,
                            type_name: TsEntityName::Ident(Ident::new(
                                "Option".into(),
                                DUMMY_SP,
                                SyntaxContext::empty(),
                            )),
                            type_params: Some(Box::new(TsTypeParamInstantiation {
                                span: DUMMY_SP,
                                params: vec![Box::new(TsType::TsTypeRef(TsTypeRef {
                                    span: DUMMY_SP,
                                    type_name: TsEntityName::Ident(Ident::new(
                                        "T".into(),
                                        DUMMY_SP,
                                        SyntaxContext::empty(),
                                    )),
                                    type_params: None,
                                }))],
                            })),
                        })),
                    })),
                }),
            }],
            decorators: vec![],
            span: DUMMY_SP,
            body: Some(BlockStmt {
                span: DUMMY_SP,
                stmts: vec![
                    // if (isNone(option)) { throw new Error("unwrap: none"); }
                    Stmt::If(IfStmt {
                        span: DUMMY_SP,
                        test: Box::new(Expr::Call(CallExpr {
                            span: DUMMY_SP,
                            callee: Callee::Expr(Box::new(Expr::Ident(Ident::new(
                                "isNone".into(),
                                DUMMY_SP,
                                SyntaxContext::empty(),
                            )))),
                            args: vec![ExprOrSpread {
                                spread: None,
                                expr: Box::new(Expr::Ident(Ident::new(
                                    "option".into(),
                                    DUMMY_SP,
                                    SyntaxContext::empty(),
                                ))),
                            }],
                            type_args: None,
                            ctxt: SyntaxContext::empty(),
                        })),
                        cons: Box::new(Stmt::Block(BlockStmt {
                            span: DUMMY_SP,
                            stmts: vec![Stmt::Throw(ThrowStmt {
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
                                            value: "unwrap: none".into(),
                                            raw: None,
                                        }))),
                                    }]),
                                    type_args: None,
                                    ctxt: SyntaxContext::empty(),
                                })),
                            })],
                            ctxt: SyntaxContext::empty(),
                        })),
                        alt: None,
                    }),
                    // return option.value;
                    Stmt::Return(ReturnStmt {
                        span: DUMMY_SP,
                        arg: Some(Box::new(Expr::Member(MemberExpr {
                            span: DUMMY_SP,
                            obj: Box::new(Expr::Ident(Ident::new(
                                "option".into(),
                                DUMMY_SP,
                                SyntaxContext::empty(),
                            ))),
                            prop: MemberProp::Ident(
                                Ident::new("value".into(), DUMMY_SP, SyntaxContext::empty()).into(),
                            ),
                        }))),
                    }),
                ],
                ctxt: SyntaxContext::empty(),
            }),
            is_generator: false,
            is_async: false,
            type_params: Some(Box::new(TsTypeParamDecl {
                span: DUMMY_SP,
                params: vec![TsTypeParam {
                    span: DUMMY_SP,
                    name: Ident::new("T".into(), DUMMY_SP, SyntaxContext::empty()),
                    constraint: None,
                    default: None,
                    is_in: false,
                    is_out: false,
                    is_const: false,
                }],
            })),
            return_type: Some(Box::new(TsTypeAnn {
                span: DUMMY_SP,
                type_ann: Box::new(TsType::TsTypeRef(TsTypeRef {
                    span: DUMMY_SP,
                    type_name: TsEntityName::Ident(Ident::new(
                        "T".into(),
                        DUMMY_SP,
                        SyntaxContext::empty(),
                    )),
                    type_params: None,
                })),
            })),
        }),
    }
}

fn generate_candid_some_function() -> FnDecl {
    FnDecl {
        ident: Ident::new("candid_some".into(), DUMMY_SP, SyntaxContext::empty()),
        declare: false,
        function: Box::new(swc_core::ecma::ast::Function {
            ctxt: SyntaxContext::empty(),
            params: vec![Param {
                span: DUMMY_SP,
                decorators: vec![],
                pat: Pat::Ident(BindingIdent {
                    id: Ident::new("value".into(), DUMMY_SP, SyntaxContext::empty()),
                    type_ann: Some(Box::new(TsTypeAnn {
                        span: DUMMY_SP,
                        type_ann: Box::new(TsType::TsTypeRef(TsTypeRef {
                            span: DUMMY_SP,
                            type_name: TsEntityName::Ident(Ident::new(
                                "T".into(),
                                DUMMY_SP,
                                SyntaxContext::empty(),
                            )),
                            type_params: None,
                        })),
                    })),
                }),
            }],
            decorators: vec![],
            span: DUMMY_SP,
            body: Some(BlockStmt {
                span: DUMMY_SP,
                stmts: vec![
                    // return [value];
                    Stmt::Return(ReturnStmt {
                        span: DUMMY_SP,
                        arg: Some(Box::new(Expr::Array(ArrayLit {
                            span: DUMMY_SP,
                            elems: vec![Some(ExprOrSpread {
                                spread: None,
                                expr: Box::new(Expr::Ident(Ident::new(
                                    "value".into(),
                                    DUMMY_SP,
                                    SyntaxContext::empty(),
                                ))),
                            })],
                        }))),
                    }),
                ],
                ctxt: SyntaxContext::empty(),
            }),
            is_generator: false,
            is_async: false,
            type_params: Some(Box::new(TsTypeParamDecl {
                span: DUMMY_SP,
                params: vec![TsTypeParam {
                    span: DUMMY_SP,
                    name: Ident::new("T".into(), DUMMY_SP, SyntaxContext::empty()),
                    constraint: None,
                    default: None,
                    is_in: false,
                    is_out: false,
                    is_const: false,
                }],
            })),
            return_type: Some(Box::new(TsTypeAnn {
                span: DUMMY_SP,
                type_ann: Box::new(TsType::TsTupleType(TsTupleType {
                    span: DUMMY_SP,
                    elem_types: vec![TsTupleElement {
                        span: DUMMY_SP,
                        label: None,
                        ty: Box::new(TsType::TsTypeRef(TsTypeRef {
                            span: DUMMY_SP,
                            type_name: TsEntityName::Ident(Ident::new(
                                "T".into(),
                                DUMMY_SP,
                                SyntaxContext::empty(),
                            )),
                            type_params: None,
                        })),
                    }],
                })),
            })),
        }),
    }
}

fn generate_candid_none_function() -> FnDecl {
    FnDecl {
        ident: Ident::new("candid_none".into(), DUMMY_SP, SyntaxContext::empty()),
        declare: false,
        function: Box::new(swc_core::ecma::ast::Function {
            ctxt: SyntaxContext::empty(),
            params: vec![],
            decorators: vec![],
            span: DUMMY_SP,
            body: Some(BlockStmt {
                span: DUMMY_SP,
                stmts: vec![
                    // return [];
                    Stmt::Return(ReturnStmt {
                        span: DUMMY_SP,
                        arg: Some(Box::new(Expr::Array(ArrayLit {
                            span: DUMMY_SP,
                            elems: vec![],
                        }))),
                    }),
                ],
                ctxt: SyntaxContext::empty(),
            }),
            is_generator: false,
            is_async: false,
            type_params: Some(Box::new(TsTypeParamDecl {
                span: DUMMY_SP,
                params: vec![TsTypeParam {
                    span: DUMMY_SP,
                    name: Ident::new("T".into(), DUMMY_SP, SyntaxContext::empty()),
                    constraint: None,
                    default: None,
                    is_in: false,
                    is_out: false,
                    is_const: false,
                }],
            })),
            return_type: Some(Box::new(TsTypeAnn {
                span: DUMMY_SP,
                type_ann: Box::new(TsType::TsTupleType(TsTupleType {
                    span: DUMMY_SP,
                    elem_types: vec![],
                })),
            })),
        }),
    }
}

// Create isSome helper function
fn create_is_some_function() -> FnDecl {
    FnDecl {
        ident: Ident::new("isSome".into(), DUMMY_SP, SyntaxContext::empty()),
        declare: false,
        function: Box::new(swc_core::ecma::ast::Function {
            params: vec![Param {
                span: DUMMY_SP,
                decorators: vec![],
                pat: Pat::Ident(BindingIdent {
                    id: Ident::new("option".into(), DUMMY_SP, SyntaxContext::empty()),
                    type_ann: Some(Box::new(TsTypeAnn {
                        span: DUMMY_SP,
                        type_ann: Box::new(TsType::TsTypeRef(TsTypeRef {
                            span: DUMMY_SP,
                            type_name: TsEntityName::Ident(Ident::new(
                                "Option".into(),
                                DUMMY_SP,
                                SyntaxContext::empty(),
                            )),
                            type_params: Some(Box::new(TsTypeParamInstantiation {
                                span: DUMMY_SP,
                                params: vec![Box::new(TsType::TsTypeRef(TsTypeRef {
                                    span: DUMMY_SP,
                                    type_name: TsEntityName::Ident(Ident::new(
                                        "T".into(),
                                        DUMMY_SP,
                                        SyntaxContext::empty(),
                                    )),
                                    type_params: None,
                                }))],
                            })),
                        })),
                    })),
                }),
            }],
            decorators: vec![],
            span: DUMMY_SP,
            body: Some(BlockStmt {
                span: DUMMY_SP,
                stmts: vec![Stmt::Return(ReturnStmt {
                    span: DUMMY_SP,
                    arg: Some(Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::EqEqEq,
                        left: Box::new(Expr::Member(MemberExpr {
                            span: DUMMY_SP,
                            obj: Box::new(Expr::Ident(Ident::new(
                                "option".into(),
                                DUMMY_SP,
                                SyntaxContext::empty(),
                            ))),
                            prop: MemberProp::Ident(
                                Ident::new("_tag".into(), DUMMY_SP, SyntaxContext::empty()).into(),
                            ),
                        })),
                        right: Box::new(Expr::Lit(Lit::Str(Str {
                            span: DUMMY_SP,
                            value: "Some".into(),
                            raw: None,
                        }))),
                    }))),
                })],
                ctxt: SyntaxContext::empty(),
            }),
            is_generator: false,
            is_async: false,
            type_params: Some(Box::new(TsTypeParamDecl {
                span: DUMMY_SP,
                params: vec![TsTypeParam {
                    span: DUMMY_SP,
                    name: Ident::new("T".into(), DUMMY_SP, SyntaxContext::empty()),
                    constraint: None,
                    default: None,
                    is_in: false,
                    is_out: false,
                    is_const: false,
                }],
            })),
            return_type: Some(Box::new(TsTypeAnn {
                span: DUMMY_SP,
                type_ann: Box::new(TsType::TsTypePredicate(TsTypePredicate {
                    span: DUMMY_SP,
                    param_name: TsThisTypeOrIdent::Ident(Ident::new(
                        "option".into(),
                        DUMMY_SP,
                        SyntaxContext::empty(),
                    )),
                    type_ann: Some(Box::new(TsTypeAnn {
                        span: DUMMY_SP,
                        type_ann: Box::new(TsType::TsTypeRef(TsTypeRef {
                            span: DUMMY_SP,
                            type_name: TsEntityName::Ident(Ident::new(
                                "Some".into(),
                                DUMMY_SP,
                                SyntaxContext::empty(),
                            )),
                            type_params: Some(Box::new(TsTypeParamInstantiation {
                                span: DUMMY_SP,
                                params: vec![Box::new(TsType::TsTypeRef(TsTypeRef {
                                    span: DUMMY_SP,
                                    type_name: TsEntityName::Ident(Ident::new(
                                        "T".into(),
                                        DUMMY_SP,
                                        SyntaxContext::empty(),
                                    )),
                                    type_params: None,
                                }))],
                            })),
                        })),
                    })),
                    asserts: false,
                })),
            })),
            ctxt: SyntaxContext::empty(),
        }),
    }
}

// Create isNone helper function
fn create_is_none_function() -> FnDecl {
    FnDecl {
        ident: Ident::new("isNone".into(), DUMMY_SP, SyntaxContext::empty()),
        declare: false,
        function: Box::new(swc_core::ecma::ast::Function {
            params: vec![Param {
                span: DUMMY_SP,
                decorators: vec![],
                pat: Pat::Ident(BindingIdent {
                    id: Ident::new("option".into(), DUMMY_SP, SyntaxContext::empty()),
                    type_ann: Some(Box::new(TsTypeAnn {
                        span: DUMMY_SP,
                        type_ann: Box::new(TsType::TsTypeRef(TsTypeRef {
                            span: DUMMY_SP,
                            type_name: TsEntityName::Ident(Ident::new(
                                "Option".into(),
                                DUMMY_SP,
                                SyntaxContext::empty(),
                            )),
                            type_params: Some(Box::new(TsTypeParamInstantiation {
                                span: DUMMY_SP,
                                params: vec![Box::new(TsType::TsTypeRef(TsTypeRef {
                                    span: DUMMY_SP,
                                    type_name: TsEntityName::Ident(Ident::new(
                                        "T".into(),
                                        DUMMY_SP,
                                        SyntaxContext::empty(),
                                    )),
                                    type_params: None,
                                }))],
                            })),
                        })),
                    })),
                }),
            }],
            decorators: vec![],
            span: DUMMY_SP,
            body: Some(BlockStmt {
                span: DUMMY_SP,
                stmts: vec![Stmt::Return(ReturnStmt {
                    span: DUMMY_SP,
                    arg: Some(Box::new(Expr::Bin(BinExpr {
                        span: DUMMY_SP,
                        op: BinaryOp::EqEqEq,
                        left: Box::new(Expr::Member(MemberExpr {
                            span: DUMMY_SP,
                            obj: Box::new(Expr::Ident(Ident::new(
                                "option".into(),
                                DUMMY_SP,
                                SyntaxContext::empty(),
                            ))),
                            prop: MemberProp::Ident(
                                Ident::new("_tag".into(), DUMMY_SP, SyntaxContext::empty()).into(),
                            ),
                        })),
                        right: Box::new(Expr::Lit(Lit::Str(Str {
                            span: DUMMY_SP,
                            value: "None".into(),
                            raw: None,
                        }))),
                    }))),
                })],
                ctxt: SyntaxContext::empty(),
            }),
            is_generator: false,
            is_async: false,
            type_params: Some(Box::new(TsTypeParamDecl {
                span: DUMMY_SP,
                params: vec![TsTypeParam {
                    span: DUMMY_SP,
                    name: Ident::new("T".into(), DUMMY_SP, SyntaxContext::empty()),
                    constraint: None,
                    default: None,
                    is_in: false,
                    is_out: false,
                    is_const: false,
                }],
            })),
            return_type: Some(Box::new(TsTypeAnn {
                span: DUMMY_SP,
                type_ann: Box::new(TsType::TsTypePredicate(TsTypePredicate {
                    span: DUMMY_SP,
                    param_name: TsThisTypeOrIdent::Ident(Ident::new(
                        "option".into(),
                        DUMMY_SP,
                        SyntaxContext::empty(),
                    )),
                    type_ann: Some(Box::new(TsTypeAnn {
                        span: DUMMY_SP,
                        type_ann: Box::new(TsType::TsTypeRef(TsTypeRef {
                            span: DUMMY_SP,
                            type_name: TsEntityName::Ident(Ident::new(
                                "None".into(),
                                DUMMY_SP,
                                SyntaxContext::empty(),
                            )),
                            type_params: None,
                        })),
                    })),
                    asserts: false,
                })),
            })),
            ctxt: SyntaxContext::empty(),
        }),
    }
}

// Create some<T>(value: T) implementation
fn create_some_function() -> FnDecl {
    use swc_core::ecma::ast::Function as SwcFunction;

    FnDecl {
        ident: Ident::new("some".into(), DUMMY_SP, SyntaxContext::empty()),
        declare: false,
        function: Box::new(SwcFunction {
            params: vec![Param {
                span: DUMMY_SP,
                decorators: vec![],
                pat: Pat::Ident(BindingIdent {
                    id: Ident::new("value".into(), DUMMY_SP, SyntaxContext::empty()),
                    type_ann: Some(Box::new(TsTypeAnn {
                        span: DUMMY_SP,
                        type_ann: Box::new(TsType::TsTypeRef(TsTypeRef {
                            span: DUMMY_SP,
                            type_name: TsEntityName::Ident(Ident::new(
                                "T".into(),
                                DUMMY_SP,
                                SyntaxContext::empty(),
                            )),
                            type_params: None,
                        })),
                    })),
                }),
            }],
            decorators: vec![],
            span: DUMMY_SP,
            body: Some(BlockStmt {
                span: DUMMY_SP,
                stmts: vec![Stmt::Return(ReturnStmt {
                    span: DUMMY_SP,
                    arg: Some(Box::new(Expr::Object(ObjectLit {
                        span: DUMMY_SP,
                        props: vec![
                            PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                                key: PropName::Ident(
                                    Ident::new("_tag".into(), DUMMY_SP, SyntaxContext::empty())
                                        .into(),
                                ),
                                value: Box::new(Expr::Lit(Lit::Str(Str {
                                    span: DUMMY_SP,
                                    value: "Some".into(),
                                    raw: None,
                                }))),
                            }))),
                            PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                                key: PropName::Ident(
                                    Ident::new("value".into(), DUMMY_SP, SyntaxContext::empty())
                                        .into(),
                                ),
                                value: Box::new(Expr::Ident(Ident::new(
                                    "value".into(),
                                    DUMMY_SP,
                                    SyntaxContext::empty(),
                                ))),
                            }))),
                        ],
                    }))),
                })],
                ctxt: SyntaxContext::empty(),
            }),
            is_generator: false,
            is_async: false,
            type_params: Some(Box::new(TsTypeParamDecl {
                span: DUMMY_SP,
                params: vec![TsTypeParam {
                    span: DUMMY_SP,
                    name: Ident::new("T".into(), DUMMY_SP, SyntaxContext::empty()),
                    constraint: None,
                    default: None,
                    is_in: false,
                    is_out: false,
                    is_const: false,
                }],
            })),
            return_type: Some(Box::new(TsTypeAnn {
                span: DUMMY_SP,
                type_ann: Box::new(TsType::TsTypeRef(TsTypeRef {
                    span: DUMMY_SP,
                    type_name: TsEntityName::Ident(Ident::new(
                        "Some".into(),
                        DUMMY_SP,
                        SyntaxContext::empty(),
                    )),
                    type_params: Some(Box::new(TsTypeParamInstantiation {
                        span: DUMMY_SP,
                        params: vec![Box::new(TsType::TsTypeRef(TsTypeRef {
                            span: DUMMY_SP,
                            type_name: TsEntityName::Ident(Ident::new(
                                "T".into(),
                                DUMMY_SP,
                                SyntaxContext::empty(),
                            )),
                            type_params: None,
                        }))],
                    })),
                })),
            })),
            ctxt: SyntaxContext::empty(),
        }),
    }
}

// Create none() implementation
fn create_none_function() -> FnDecl {
    use swc_core::ecma::ast::Function as SwcFunction;

    FnDecl {
        ident: Ident::new("none".into(), DUMMY_SP, SyntaxContext::empty()),
        declare: false,
        function: Box::new(SwcFunction {
            params: vec![],
            decorators: vec![],
            span: DUMMY_SP,
            body: Some(BlockStmt {
                span: DUMMY_SP,
                stmts: vec![Stmt::Return(ReturnStmt {
                    span: DUMMY_SP,
                    arg: Some(Box::new(Expr::Object(ObjectLit {
                        span: DUMMY_SP,
                        props: vec![PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                            key: PropName::Ident(
                                Ident::new("_tag".into(), DUMMY_SP, SyntaxContext::empty()).into(),
                            ),
                            value: Box::new(Expr::Lit(Lit::Str(Str {
                                span: DUMMY_SP,
                                value: "None".into(),
                                raw: None,
                            }))),
                        })))],
                    }))),
                })],
                ctxt: SyntaxContext::empty(),
            }),
            is_generator: false,
            is_async: false,
            type_params: None,
            return_type: Some(Box::new(TsTypeAnn {
                span: DUMMY_SP,
                type_ann: Box::new(TsType::TsTypeRef(TsTypeRef {
                    span: DUMMY_SP,
                    type_name: TsEntityName::Ident(Ident::new(
                        "None".into(),
                        DUMMY_SP,
                        SyntaxContext::empty(),
                    )),
                    type_params: None,
                })),
            })),
            ctxt: SyntaxContext::empty(),
        }),
    }
}

fn create_some_type() -> TsInterfaceDecl {
    TsInterfaceDecl {
        span: DUMMY_SP,
        declare: false,
        id: Ident::new("Some".into(), DUMMY_SP, SyntaxContext::empty()),
        type_params: Some(Box::new(TsTypeParamDecl {
            span: DUMMY_SP,
            params: vec![TsTypeParam {
                span: DUMMY_SP,
                name: Ident::new("T".into(), DUMMY_SP, SyntaxContext::empty()),
                constraint: None,
                default: None,
                is_in: false,
                is_out: false,
                is_const: false,
            }],
        })),
        extends: vec![],
        body: TsInterfaceBody {
            span: DUMMY_SP,
            body: vec![
                TsTypeElement::TsPropertySignature(TsPropertySignature {
                    span: DUMMY_SP,
                    readonly: false,
                    key: Box::new(Expr::Ident(Ident::new(
                        "_tag".into(),
                        DUMMY_SP,
                        SyntaxContext::empty(),
                    ))),
                    computed: false,
                    optional: false,
                    type_ann: Some(Box::new(TsTypeAnn {
                        span: DUMMY_SP,
                        type_ann: Box::new(TsType::TsLitType(TsLitType {
                            span: DUMMY_SP,
                            lit: TsLit::Str(Str {
                                span: DUMMY_SP,
                                value: "Some".into(),
                                raw: None,
                            }),
                        })),
                    })),
                }),
                TsTypeElement::TsPropertySignature(TsPropertySignature {
                    span: DUMMY_SP,
                    readonly: false,
                    key: Box::new(Expr::Ident(Ident::new(
                        "value".into(),
                        DUMMY_SP,
                        SyntaxContext::empty(),
                    ))),
                    computed: false,
                    optional: false,
                    type_ann: Some(Box::new(TsTypeAnn {
                        span: DUMMY_SP,
                        type_ann: Box::new(TsType::TsTypeRef(TsTypeRef {
                            span: DUMMY_SP,
                            type_name: TsEntityName::Ident(Ident::new(
                                "T".into(),
                                DUMMY_SP,
                                SyntaxContext::empty(),
                            )),
                            type_params: None,
                        })),
                    })),
                }),
            ],
        },
    }
}

fn create_none_type() -> TsInterfaceDecl {
    TsInterfaceDecl {
        span: DUMMY_SP,
        declare: false,
        id: Ident::new("None".into(), DUMMY_SP, SyntaxContext::empty()),
        type_params: None,
        extends: vec![],
        body: TsInterfaceBody {
            span: DUMMY_SP,
            body: vec![TsTypeElement::TsPropertySignature(TsPropertySignature {
                span: DUMMY_SP,
                readonly: false,
                key: Box::new(Expr::Ident(Ident::new(
                    "_tag".into(),
                    DUMMY_SP,
                    SyntaxContext::empty(),
                ))),
                computed: false,
                optional: false,
                type_ann: Some(Box::new(TsTypeAnn {
                    span: DUMMY_SP,
                    type_ann: Box::new(TsType::TsLitType(TsLitType {
                        span: DUMMY_SP,
                        lit: TsLit::Str(Str {
                            span: DUMMY_SP,
                            value: "None".into(),
                            raw: None,
                        }),
                    })),
                })),
            })],
        },
    }
}

fn create_option_type() -> TsTypeAliasDecl {
    TsTypeAliasDecl {
        span: DUMMY_SP,
        declare: false,
        id: Ident::new("Option".into(), DUMMY_SP, SyntaxContext::empty()),
        type_params: Some(Box::new(TsTypeParamDecl {
            span: DUMMY_SP,
            params: vec![TsTypeParam {
                span: DUMMY_SP,
                name: Ident::new("T".into(), DUMMY_SP, SyntaxContext::empty()),
                constraint: None,
                default: None,
                is_in: false,
                is_out: false,
                is_const: false,
            }],
        })),
        type_ann: Box::new(TsType::TsUnionOrIntersectionType(
            TsUnionOrIntersectionType::TsUnionType(TsUnionType {
                span: DUMMY_SP,
                types: vec![
                    Box::new(TsType::TsTypeRef(TsTypeRef {
                        span: DUMMY_SP,
                        type_name: TsEntityName::Ident(Ident::new(
                            "Some".into(),
                            DUMMY_SP,
                            SyntaxContext::empty(),
                        )),
                        type_params: Some(Box::new(TsTypeParamInstantiation {
                            span: DUMMY_SP,
                            params: vec![Box::new(TsType::TsTypeRef(TsTypeRef {
                                span: DUMMY_SP,
                                type_name: TsEntityName::Ident(Ident::new(
                                    "T".into(),
                                    DUMMY_SP,
                                    SyntaxContext::empty(),
                                )),
                                type_params: None,
                            }))],
                        })),
                    })),
                    Box::new(TsType::TsTypeRef(TsTypeRef {
                        span: DUMMY_SP,
                        type_name: TsEntityName::Ident(Ident::new(
                            "None".into(),
                            DUMMY_SP,
                            SyntaxContext::empty(),
                        )),
                        type_params: None,
                    })),
                ],
            }),
        )),
    }
}

// Generate a function to extract the actual error message from IC agent errors
fn generate_extract_agent_error_function() -> FnDecl {
    FnDecl {
        ident: Ident::new(
            "extractAgentErrorMessage".into(),
            DUMMY_SP,
            SyntaxContext::empty(),
        ),
        declare: false,
        function: Box::new(Function {
            params: vec![Param {
                span: DUMMY_SP,
                decorators: vec![],
                pat: Pat::Ident(BindingIdent {
                    id: Ident::new("error".into(), DUMMY_SP, SyntaxContext::empty()),
                    type_ann: Some(Box::new(TsTypeAnn {
                        span: DUMMY_SP,
                        type_ann: Box::new(TsType::TsKeywordType(TsKeywordType {
                            span: DUMMY_SP,
                            kind: TsKeywordTypeKind::TsStringKeyword,
                        })),
                    })),
                }),
            }],
            decorators: vec![],
            span: DUMMY_SP,
            body: Some(BlockStmt {
                span: DUMMY_SP,
                stmts: vec![
                    // const errorString = String(error);
                    Stmt::Decl(Decl::Var(Box::new(VarDecl {
                        span: DUMMY_SP,
                        kind: VarDeclKind::Const,
                        declare: false,
                        decls: vec![VarDeclarator {
                            span: DUMMY_SP,
                            name: Pat::Ident(BindingIdent {
                                id: Ident::new(
                                    "errorString".into(),
                                    DUMMY_SP,
                                    SyntaxContext::empty(),
                                ),
                                type_ann: None,
                            }),
                            init: Some(Box::new(Expr::Call(CallExpr {
                                span: DUMMY_SP,
                                callee: Callee::Expr(Box::new(Expr::Ident(Ident::new(
                                    "String".into(),
                                    DUMMY_SP,
                                    SyntaxContext::empty(),
                                )))),
                                args: vec![ExprOrSpread {
                                    spread: None,
                                    expr: Box::new(Expr::Ident(Ident::new(
                                        "error".into(),
                                        DUMMY_SP,
                                        SyntaxContext::empty(),
                                    ))),
                                }],
                                type_args: None,
                                ctxt: SyntaxContext::empty(),
                            }))),
                            definite: false,
                        }],
                        ctxt: SyntaxContext::empty(),
                    }))),
                    // const match = errorString.match(/with message: '([^']+)'/);
                    Stmt::Decl(Decl::Var(Box::new(VarDecl {
                        span: DUMMY_SP,
                        kind: VarDeclKind::Const,
                        declare: false,
                        decls: vec![VarDeclarator {
                            span: DUMMY_SP,
                            name: Pat::Ident(BindingIdent {
                                id: Ident::new("match".into(), DUMMY_SP, SyntaxContext::empty()),
                                type_ann: None,
                            }),
                            init: Some(Box::new(Expr::Call(CallExpr {
                                span: DUMMY_SP,
                                callee: Callee::Expr(Box::new(Expr::Member(MemberExpr {
                                    span: DUMMY_SP,
                                    obj: Box::new(Expr::Ident(Ident::new(
                                        "errorString".into(),
                                        DUMMY_SP,
                                        SyntaxContext::empty(),
                                    ))),
                                    prop: MemberProp::Ident(
                                        Ident::new(
                                            "match".into(),
                                            DUMMY_SP,
                                            SyntaxContext::empty(),
                                        )
                                        .into(),
                                    ),
                                }))),
                                args: vec![ExprOrSpread {
                                    spread: None,
                                    expr: Box::new(Expr::Lit(Lit::Regex(Regex {
                                        span: DUMMY_SP,
                                        exp: "with message: '([^']+)'".into(),
                                        flags: "".into(),
                                    }))),
                                }],
                                type_args: None,
                                ctxt: SyntaxContext::empty(),
                            }))),
                            definite: false,
                        }],
                        ctxt: SyntaxContext::empty(),
                    }))),
                    // return match ? match[1] : errorString;
                    Stmt::Return(ReturnStmt {
                        span: DUMMY_SP,
                        arg: Some(Box::new(Expr::Cond(CondExpr {
                            span: DUMMY_SP,
                            test: Box::new(Expr::Ident(Ident::new(
                                "match".into(),
                                DUMMY_SP,
                                SyntaxContext::empty(),
                            ))),
                            cons: Box::new(Expr::Member(MemberExpr {
                                span: DUMMY_SP,
                                obj: Box::new(Expr::Ident(Ident::new(
                                    "match".into(),
                                    DUMMY_SP,
                                    SyntaxContext::empty(),
                                ))),
                                prop: MemberProp::Computed(ComputedPropName {
                                    span: DUMMY_SP,
                                    expr: Box::new(Expr::Lit(Lit::Num(Number {
                                        span: DUMMY_SP,
                                        value: 1.0,
                                        raw: None,
                                    }))),
                                }),
                            })),
                            alt: Box::new(Expr::Ident(Ident::new(
                                "errorString".into(),
                                DUMMY_SP,
                                SyntaxContext::empty(),
                            ))),
                        }))),
                    }),
                ],
                ctxt: SyntaxContext::empty(),
            }),
            is_generator: false,
            is_async: false,
            type_params: None,
            return_type: Some(Box::new(TsTypeAnn {
                span: DUMMY_SP,
                type_ann: Box::new(TsType::TsKeywordType(TsKeywordType {
                    span: DUMMY_SP,
                    kind: TsKeywordTypeKind::TsStringKeyword,
                })),
            })),
            ctxt: SyntaxContext::empty(),
        }),
    }
}
