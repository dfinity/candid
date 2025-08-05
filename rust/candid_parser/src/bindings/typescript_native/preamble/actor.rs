use swc_core::common::{SyntaxContext, DUMMY_SP};
use swc_core::ecma::ast::*;

use super::super::ident::get_ident_guarded;

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
                                    type_name: TsEntityName::Ident(get_ident_guarded(&format!(
                                        "{}Interface",
                                        service_name
                                    ))),
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
