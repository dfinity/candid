use swc_core::common::{SyntaxContext, DUMMY_SP};
use swc_core::ecma::ast::*;

pub fn interface_options_utils(module: &mut Module) {
    let some_type = create_some_type();
    module
        .body
        .push(ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl {
            span: DUMMY_SP,
            decl: Decl::TsInterface(Box::new(some_type)),
        })));

    let none_type = create_none_type();
    module
        .body
        .push(ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl {
            span: DUMMY_SP,
            decl: Decl::TsInterface(Box::new(none_type)),
        })));

    let option_type = create_option_type();
    module
        .body
        .push(ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl {
            span: DUMMY_SP,
            decl: Decl::TsTypeAlias(Box::new(option_type)),
        })));
}

pub fn wrapper_options_utils(module: &mut Module) {
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
                                Ident::new("__kind__".into(), DUMMY_SP, SyntaxContext::empty())
                                    .into(),
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
                                Ident::new("__kind__".into(), DUMMY_SP, SyntaxContext::empty())
                                    .into(),
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
                                    Ident::new("__kind__".into(), DUMMY_SP, SyntaxContext::empty())
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
                                Ident::new("__kind__".into(), DUMMY_SP, SyntaxContext::empty())
                                    .into(),
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
                        "__kind__".into(),
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
                    "__kind__".into(),
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
