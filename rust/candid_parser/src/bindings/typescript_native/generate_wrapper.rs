use candid::types::{Field, Function, Label, Type, TypeEnv, TypeInner};
use swc_core::common::{SyntaxContext, DUMMY_SP};
use swc_core::ecma::ast::*;

/// Provides functions to generate JavaScript expressions that convert
/// between TypeScript and Candid representations.
pub struct TypeConverter<'a> {
    env: &'a TypeEnv,
}

impl<'a> TypeConverter<'a> {
    /// Create a new TypeConverter with the given type environment
    pub fn new(env: &'a TypeEnv) -> Self {
        TypeConverter { env }
    }

    /// Generate an expression that converts from TypeScript to Candid representation
    /// for the given Candid type and expression.
    pub fn to_candid(&self, expr: &Expr, ty: &Type) -> Expr {
        self._to_candid(expr, ty)
    }

    fn _to_candid(&self, expr: &Expr, ty: &Type) -> Expr {
        match ty.as_ref() {
            TypeInner::Null => self.convert_null(expr),
            TypeInner::Bool => expr.clone(),
            TypeInner::Nat
            | TypeInner::Int
            | TypeInner::Nat64
            | TypeInner::Int64
            | TypeInner::Nat8
            | TypeInner::Nat16
            | TypeInner::Nat32
            | TypeInner::Int8
            | TypeInner::Int16
            | TypeInner::Int32
            | TypeInner::Float32
            | TypeInner::Float64 => expr.clone(),
            TypeInner::Text => expr.clone(),
            TypeInner::Reserved => expr.clone(),
            TypeInner::Empty => self.convert_empty(expr),
            TypeInner::Principal => self.convert_principal_to_candid(expr),
            TypeInner::Opt(ref inner) => self.convert_opt_to_candid(expr, inner),
            TypeInner::Vec(ref inner) => self.convert_vec_to_candid(expr, inner),
            TypeInner::Record(ref fields) => self.convert_record_to_candid(expr, fields),
            TypeInner::Variant(ref _fields) => expr.clone(), //self.convert_variant_to_candid(expr, fields),
            TypeInner::Func(ref func) => self.convert_func_to_candid(expr, func),
            TypeInner::Service(_) => self.convert_service_to_candid(expr),
            TypeInner::Var(ref id) => self.convert_var_to_candid(expr, id),
            // For unsupported types, we pass through unchanged
            _ => expr.clone(),
        }
    }

    /// Generate an expression that converts from Candid to TypeScript representation
    /// for the given Candid type and expression.
    pub fn from_candid(&self, expr: &Expr, ty: &Type) -> Expr {
        self._from_candid(expr, ty)
    }

    fn _from_candid(&self, expr: &Expr, ty: &Type) -> Expr {
        match ty.as_ref() {
            TypeInner::Null => self.convert_null(expr),
            TypeInner::Bool => expr.clone(),
            TypeInner::Nat | TypeInner::Int | TypeInner::Nat64 | TypeInner::Int64 => {
                self.convert_from_bigint(expr)
            }
            TypeInner::Nat8
            | TypeInner::Nat16
            | TypeInner::Nat32
            | TypeInner::Int8
            | TypeInner::Int16
            | TypeInner::Int32
            | TypeInner::Float32
            | TypeInner::Float64 => expr.clone(),
            TypeInner::Text => expr.clone(),
            TypeInner::Reserved => expr.clone(),
            TypeInner::Empty => self.convert_empty(expr),
            TypeInner::Principal => self.convert_principal_from_candid(expr),
            TypeInner::Opt(ref inner) => self.convert_opt_from_candid(expr, inner),
            TypeInner::Vec(ref inner) => self.convert_vec_from_candid(expr, inner),
            TypeInner::Record(ref fields) => self.convert_record_from_candid(expr, fields),
            TypeInner::Variant(ref _fields) => expr.clone(), //self.convert_variant_from_candid(expr, fields)
            TypeInner::Func(ref func) => self.convert_func_from_candid(expr, func),
            TypeInner::Service(_) => self.convert_service_from_candid(expr),
            TypeInner::Var(ref id) => self.convert_var_from_candid(expr, id),
            // For unsupported types, we pass through unchanged
            _ => expr.clone(),
        }
    }

    // --- Type-specific conversion methods ---

    fn convert_null(&self, expr: &Expr) -> Expr {
        expr.clone()
    }

    fn convert_empty(&self, _expr: &Expr) -> Expr {
        // Empty type is represented as null in JavaScript
        Expr::Lit(Lit::Null(Null { span: DUMMY_SP }))
    }

    fn convert_from_bigint(&self, expr: &Expr) -> Expr {
        // Convert from Candid bigint to JavaScript BigInt
        expr.clone() // BigInt is already handled correctly in this direction
    }

    fn convert_principal_to_candid(&self, expr: &Expr) -> Expr {
        // Convert from JavaScript Principal to Candid Principal
        expr.clone() // Principal object is already compatible
    }

    fn convert_principal_from_candid(&self, expr: &Expr) -> Expr {
        // Convert from Candid Principal to JavaScript Principal
        expr.clone() // Principal object is already compatible
    }

    fn convert_opt_to_candid(&self, expr: &Expr, inner: &Type) -> Expr {
        // Count the nesting depth
        fn count_nesting_depth(ty: &Type) -> usize {
            match ty.as_ref() {
                TypeInner::Opt(inner) => 1 + count_nesting_depth(inner),
                _ => 0,
            }
        }

        let depth = count_nesting_depth(inner);

        if depth == 0 {
            // Base case (T | null)
            return Expr::Cond(CondExpr {
                span: DUMMY_SP,
                test: Box::new(Expr::Bin(BinExpr {
                    span: DUMMY_SP,
                    op: BinaryOp::EqEqEq,
                    left: Box::new(expr.clone()),
                    right: Box::new(Expr::Lit(Lit::Null(Null { span: DUMMY_SP }))),
                })),
                cons: Box::new(Expr::Call(CallExpr {
                    span: DUMMY_SP,
                    callee: Callee::Expr(Box::new(Expr::Ident(Ident::new(
                        "candid_none".into(),
                        DUMMY_SP,
                        SyntaxContext::empty(),
                    )))),
                    args: vec![],
                    type_args: None,
                    ctxt: SyntaxContext::empty(),
                })),
                alt: Box::new(Expr::Call(CallExpr {
                    span: DUMMY_SP,
                    callee: Callee::Expr(Box::new(Expr::Ident(Ident::new(
                        "candid_some".into(),
                        DUMMY_SP,
                        SyntaxContext::empty(),
                    )))),
                    args: vec![ExprOrSpread {
                        spread: None,
                        expr: Box::new(expr.clone()),
                    }],
                    type_args: None,
                    ctxt: SyntaxContext::empty(),
                })),
            });
        } else {
            // Handle the outermost Option check
            let is_none_check = Expr::Call(CallExpr {
                span: DUMMY_SP,
                callee: Callee::Expr(Box::new(Expr::Ident(Ident::new(
                    "isNone".into(),
                    DUMMY_SP,
                    SyntaxContext::empty(),
                )))),
                args: vec![ExprOrSpread {
                    spread: None,
                    expr: Box::new(expr.clone()),
                }],
                type_args: None,
                ctxt: SyntaxContext::empty(),
            });

            // Create the unwrap call
            let unwrap_call = Expr::Call(CallExpr {
                span: DUMMY_SP,
                callee: Callee::Expr(Box::new(Expr::Ident(Ident::new(
                    "unwrap".into(),
                    DUMMY_SP,
                    SyntaxContext::empty(),
                )))),
                args: vec![ExprOrSpread {
                    spread: None,
                    expr: Box::new(expr.clone()),
                }],
                type_args: None,
                ctxt: SyntaxContext::empty(),
            });

            // For deeper nesting (depth >= 2), create nested conditional structure
            let current_expr = unwrap_call;

            // Create the innermost check first
            let innermost_check = Expr::Cond(CondExpr {
                span: DUMMY_SP,
                test: Box::new(Expr::Bin(BinExpr {
                    span: DUMMY_SP,
                    op: BinaryOp::EqEqEq,
                    left: Box::new(current_expr.clone()),
                    right: Box::new(Expr::Lit(Lit::Null(Null { span: DUMMY_SP }))),
                })),
                cons: Box::new(Expr::Call(CallExpr {
                    span: DUMMY_SP,
                    callee: Callee::Expr(Box::new(Expr::Ident(Ident::new(
                        "candid_none".into(),
                        DUMMY_SP,
                        SyntaxContext::empty(),
                    )))),
                    args: vec![],
                    type_args: None,
                    ctxt: SyntaxContext::empty(),
                })),
                alt: Box::new(Expr::Call(CallExpr {
                    span: DUMMY_SP,
                    callee: Callee::Expr(Box::new(Expr::Ident(Ident::new(
                        "candid_some".into(),
                        DUMMY_SP,
                        SyntaxContext::empty(),
                    )))),
                    args: vec![ExprOrSpread {
                        spread: None,
                        expr: Box::new(current_expr),
                    }],
                    type_args: None,
                    ctxt: SyntaxContext::empty(),
                })),
            });

            // Wrap with the outermost check
            Expr::Cond(CondExpr {
                span: DUMMY_SP,
                test: Box::new(is_none_check),
                cons: Box::new(Expr::Call(CallExpr {
                    span: DUMMY_SP,
                    callee: Callee::Expr(Box::new(Expr::Ident(Ident::new(
                        "candid_none".into(),
                        DUMMY_SP,
                        SyntaxContext::empty(),
                    )))),
                    args: vec![],
                    type_args: None,
                    ctxt: SyntaxContext::empty(),
                })),
                alt: Box::new(Expr::Call(CallExpr {
                    span: DUMMY_SP,
                    callee: Callee::Expr(Box::new(Expr::Ident(Ident::new(
                        "candid_some".into(),
                        DUMMY_SP,
                        SyntaxContext::empty(),
                    )))),
                    args: vec![ExprOrSpread {
                        spread: None,
                        expr: Box::new(innermost_check),
                    }],
                    type_args: None,
                    ctxt: SyntaxContext::empty(),
                })),
            })
        }
    }

    // Helper method to count the nesting depth of optional types
    fn count_opt_nesting_depth(&self, ty: &Type) -> usize {
        match ty.as_ref() {
            TypeInner::Opt(inner) => 1 + self.count_opt_nesting_depth(inner),
            _ => 0,
        }
    }

    fn convert_opt_from_candid(&self, expr: &Expr, inner: &Type) -> Expr {
        // Count the nesting depth of optionals
        let depth = self.count_opt_nesting_depth(inner);

        // If depth is 1, use the base case conversion (T | null)
        if depth == 0 {
            self.convert_base_optional(expr, inner)
        } else if depth > 0 {
            // For nested optionals, use the recursive conversion
            self.convert_nested_optional(expr, inner, depth)
        } else {
            // Shouldn't happen
            expr.clone()
        }
    }

    // Base function: EXPR.length === 0 ? null : EXPR[0]
    fn convert_base_optional(&self, expr: &Expr, inner: &Type) -> Expr {
        // Get the inner non-optional type
        let base_type = if let TypeInner::Opt(ref inner_ty) = inner.as_ref() {
            inner_ty
        } else {
            inner // Shouldn't happen
        };

        // Create a length check: expr.length === 0
        let length_check = Expr::Bin(BinExpr {
            span: DUMMY_SP,
            op: BinaryOp::EqEqEq,
            left: Box::new(Expr::Member(MemberExpr {
                span: DUMMY_SP,
                obj: Box::new(expr.clone()),
                prop: MemberProp::Ident(
                    Ident::new("length".into(), DUMMY_SP, SyntaxContext::empty()).into(),
                ),
            })),
            right: Box::new(Expr::Lit(Lit::Num(Number {
                span: DUMMY_SP,
                value: 0.0,
                raw: None,
            }))),
        });

        // Create a null literal for the "empty" case
        let null_expr = Expr::Lit(Lit::Null(Null { span: DUMMY_SP }));

        // Create an expression to access the first element: expr[0]
        let first_element = Expr::Member(MemberExpr {
            span: DUMMY_SP,
            obj: Box::new(expr.clone()),
            prop: MemberProp::Computed(ComputedPropName {
                span: DUMMY_SP,
                expr: Box::new(Expr::Lit(Lit::Num(Number {
                    span: DUMMY_SP,
                    value: 0.0,
                    raw: None,
                }))),
            }),
        });

        // Convert the first element if needed
        let converted_element = self._from_candid(&first_element, base_type);

        // Create the conditional: expr.length === 0 ? null : expr[0]
        Expr::Cond(CondExpr {
            span: DUMMY_SP,
            test: Box::new(length_check),
            cons: Box::new(null_expr),
            alt: Box::new(converted_element),
        })
    }

    // Recursive function: EXPR.length === 0 ? none() : some(INTERNAL_CALL_REC(EXPR[0]))
    fn convert_nested_optional(&self, expr: &Expr, inner: &Type, depth: usize) -> Expr {
        // Create a length check: expr.length === 0
        let length_check = Expr::Bin(BinExpr {
            span: DUMMY_SP,
            op: BinaryOp::EqEqEq,
            left: Box::new(Expr::Member(MemberExpr {
                span: DUMMY_SP,
                obj: Box::new(expr.clone()),
                prop: MemberProp::Ident(
                    Ident::new("length".into(), DUMMY_SP, SyntaxContext::empty()).into(),
                ),
            })),
            right: Box::new(Expr::Lit(Lit::Num(Number {
                span: DUMMY_SP,
                value: 0.0,
                raw: None,
            }))),
        });

        // Create none() call for the "empty" case
        let none_expr = Expr::Call(CallExpr {
            span: DUMMY_SP,
            callee: Callee::Expr(Box::new(Expr::Ident(Ident::new(
                "none".into(),
                DUMMY_SP,
                SyntaxContext::empty(),
            )))),
            args: vec![],
            type_args: None,
            ctxt: SyntaxContext::empty(),
        });

        // Create an expression to access the first element: expr[0]
        let first_element = Expr::Member(MemberExpr {
            span: DUMMY_SP,
            obj: Box::new(expr.clone()),
            prop: MemberProp::Computed(ComputedPropName {
                span: DUMMY_SP,
                expr: Box::new(Expr::Lit(Lit::Num(Number {
                    span: DUMMY_SP,
                    value: 0.0,
                    raw: None,
                }))),
            }),
        });

        // Get the inner type (unwrap one level of optional)
        let next_inner = if let TypeInner::Opt(ref inner_ty) = inner.as_ref() {
            inner_ty
        } else {
            inner // Shouldn't happen
        };

        // For the inner value, we need to either:
        // - Recursively call this function (for depth > 1)
        // - Use the base case (for depth == 1)
        let inner_expr = if depth > 1 {
            self.convert_nested_optional(&first_element, next_inner, depth - 1)
        } else {
            // At depth 2, the inner value is a base case (T | null)
            self.convert_base_optional(&first_element, next_inner)
        };

        // Wrap the inner expression in some()
        let some_expr = Expr::Call(CallExpr {
            span: DUMMY_SP,
            callee: Callee::Expr(Box::new(Expr::Ident(Ident::new(
                "some".into(),
                DUMMY_SP,
                SyntaxContext::empty(),
            )))),
            args: vec![ExprOrSpread {
                spread: None,
                expr: Box::new(inner_expr),
            }],
            type_args: None,
            ctxt: SyntaxContext::empty(),
        });

        // Create the conditional: expr.length === 0 ? none() : some(...)
        Expr::Cond(CondExpr {
            span: DUMMY_SP,
            test: Box::new(length_check),
            cons: Box::new(none_expr),
            alt: Box::new(some_expr),
        })
    }

    // *** Array conversion methods ***

    fn convert_vec_to_candid(&self, expr: &Expr, inner: &Type) -> Expr {
        // Check if it's a number array that should be converted to a typed array
        match inner.as_ref() {
            TypeInner::Nat8
            | TypeInner::Int8
            | TypeInner::Nat16
            | TypeInner::Int16
            | TypeInner::Nat32
            | TypeInner::Int32
            | TypeInner::Nat64
            | TypeInner::Int64 => {
                // Handle conversion from regular array to TypedArray if needed
                return expr.clone();
            }
            _ => {
                // Generate map to convert each element
                Expr::Call(CallExpr {
                    span: DUMMY_SP,
                    callee: Callee::Expr(Box::new(Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(expr.clone()),
                        prop: MemberProp::Ident(
                            Ident::new("map".into(), DUMMY_SP, SyntaxContext::empty()).into(),
                        ),
                    }))),
                    args: vec![ExprOrSpread {
                        spread: None,
                        expr: Box::new(Expr::Arrow(ArrowExpr {
                            span: DUMMY_SP,
                            params: vec![Pat::Ident(BindingIdent {
                                id: Ident::new("x".into(), DUMMY_SP, SyntaxContext::empty()),
                                type_ann: None,
                            })],
                            body: Box::new(BlockStmtOrExpr::BlockStmt(BlockStmt {
                                span: DUMMY_SP,
                                stmts: vec![Stmt::Return(ReturnStmt {
                                    span: DUMMY_SP,
                                    arg: Some(Box::new(self._to_candid(
                                        &Expr::Ident(Ident::new(
                                            "x".into(),
                                            DUMMY_SP,
                                            SyntaxContext::empty(),
                                        )),
                                        inner,
                                    ))),
                                })],
                                ctxt: SyntaxContext::empty(),
                            })),
                            is_async: false,
                            is_generator: false,
                            type_params: None,
                            return_type: None,
                            ctxt: SyntaxContext::empty(),
                        })),
                    }],
                    type_args: None,
                    ctxt: SyntaxContext::empty(),
                })
            }
        }
    }

    fn convert_number_array_to_typed_array(&self, expr: &Expr, inner: &Type) -> Expr {
        // Get the appropriate TypedArray constructor based on the element type
        let constructor = match inner.as_ref() {
            TypeInner::Nat8 => "Uint8Array",
            TypeInner::Int8 => "Int8Array",
            TypeInner::Nat16 => "Uint16Array",
            TypeInner::Int16 => "Int16Array",
            TypeInner::Nat32 => "Uint32Array",
            TypeInner::Int32 => "Int32Array",
            TypeInner::Nat64 => "BigUint64Array",
            TypeInner::Int64 => "BigInt64Array",
            _ => return expr.clone(), // Should not happen given the caller's check
        };

        // Create TypedArray from regular array
        Expr::New(NewExpr {
            span: DUMMY_SP,
            callee: Box::new(Expr::Ident(Ident::new(
                constructor.into(),
                DUMMY_SP,
                SyntaxContext::empty(),
            ))),
            args: Some(vec![ExprOrSpread {
                spread: None,
                expr: Box::new(expr.clone()),
            }]),
            type_args: None,
            ctxt: SyntaxContext::empty(),
        })
    }

    fn convert_vec_from_candid(&self, expr: &Expr, inner: &Type) -> Expr {
        // Check if it's a typed array that should be converted to a regular array
        match inner.as_ref() {
            TypeInner::Nat8
            | TypeInner::Int8
            | TypeInner::Nat16
            | TypeInner::Int16
            | TypeInner::Nat32
            | TypeInner::Int32
            | TypeInner::Nat64
            | TypeInner::Int64 => {
                // Handle conversion from TypedArray to regular array if needed
                self.convert_typed_array_to_array(expr, inner)
            }
            _ => {
                // Generate map to convert each element
                // Generate map to convert each element
                // Generate map to convert each element
                Expr::Call(CallExpr {
                    span: DUMMY_SP,
                    callee: Callee::Expr(Box::new(Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(expr.clone()),
                        prop: MemberProp::Ident(
                            Ident::new("map".into(), DUMMY_SP, SyntaxContext::empty()).into(),
                        ),
                    }))),
                    args: vec![ExprOrSpread {
                        spread: None,
                        expr: Box::new(Expr::Arrow(ArrowExpr {
                            span: DUMMY_SP,
                            params: vec![Pat::Ident(BindingIdent {
                                id: Ident::new("x".into(), DUMMY_SP, SyntaxContext::empty()),
                                type_ann: None,
                            })],
                            body: Box::new(BlockStmtOrExpr::BlockStmt(BlockStmt {
                                span: DUMMY_SP,
                                stmts: vec![Stmt::Return(ReturnStmt {
                                    span: DUMMY_SP,
                                    arg: Some(Box::new(self._from_candid(
                                        &Expr::Ident(Ident::new(
                                            "x".into(),
                                            DUMMY_SP,
                                            SyntaxContext::empty(),
                                        )),
                                        inner,
                                    ))),
                                })],
                                ctxt: SyntaxContext::empty(),
                            })),
                            is_async: false,
                            is_generator: false,
                            type_params: None,
                            return_type: None,
                            ctxt: SyntaxContext::empty(),
                        })),
                    }],
                    type_args: None,
                    ctxt: SyntaxContext::empty(),
                })
            }
        }
    }

    fn convert_typed_array_to_array(&self, expr: &Expr, _inner: &Type) -> Expr {
        // Convert TypedArray to Array using Array.from
        Expr::Call(CallExpr {
            span: DUMMY_SP,
            callee: Callee::Expr(Box::new(Expr::Member(MemberExpr {
                span: DUMMY_SP,
                obj: Box::new(Expr::Ident(Ident::new(
                    "Array".into(),
                    DUMMY_SP,
                    SyntaxContext::empty(),
                ))),
                prop: MemberProp::Ident(
                    Ident::new("from".into(), DUMMY_SP, SyntaxContext::empty()).into(),
                ),
            }))),
            args: vec![ExprOrSpread {
                spread: None,
                expr: Box::new(expr.clone()),
            }],
            type_args: None,
            ctxt: SyntaxContext::empty(),
        })
    }

    fn convert_record_to_candid(&self, expr: &Expr, fields: &[Field]) -> Expr {
        // If the record is a tuple, handle differently
        if self.is_tuple(fields) {
            return self.convert_tuple_to_candid(expr, fields);
        }

        // Create a new object with converted fields
        Expr::Object(ObjectLit {
            span: DUMMY_SP,
            props: fields
                .iter()
                .map(|field| {
                    let key = match &*field.id {
                        Label::Named(name) => PropName::Ident(
                            Ident::new(name.clone().into(), DUMMY_SP, SyntaxContext::empty())
                                .into(),
                        ),
                        Label::Id(n) | Label::Unnamed(n) => PropName::Ident(
                            Ident::new(format!("_{}_", n).into(), DUMMY_SP, SyntaxContext::empty())
                                .into(),
                        ),
                    };

                    // Get the field from the input object
                    let field_expr = Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(expr.clone()),
                        prop: match &*field.id {
                            Label::Named(name) => MemberProp::Ident(
                                Ident::new(name.clone().into(), DUMMY_SP, SyntaxContext::empty())
                                    .into(),
                            ),
                            Label::Id(n) | Label::Unnamed(n) => MemberProp::Ident(
                                Ident::new(
                                    format!("_{}_", n).into(),
                                    DUMMY_SP,
                                    SyntaxContext::empty(),
                                )
                                .into(),
                            ),
                        },
                    });

                    // Convert the field value
                    let value = match field.ty.as_ref() {
                        TypeInner::Opt(inner) => {
                            // For optional fields, use JavaScript truthiness check
                            Expr::Cond(CondExpr {
                                span: DUMMY_SP,
                                test: Box::new(field_expr.clone()),
                                cons: Box::new(Expr::Call(CallExpr {
                                    span: DUMMY_SP,
                                    callee: Callee::Expr(Box::new(Expr::Ident(Ident::new(
                                        "candid_some".into(),
                                        DUMMY_SP,
                                        SyntaxContext::empty(),
                                    )))),
                                    args: vec![ExprOrSpread {
                                        spread: None,
                                        expr: Box::new(self._to_candid(&field_expr, inner)),
                                    }],
                                    type_args: None,
                                    ctxt: SyntaxContext::empty(),
                                })),
                                alt: Box::new(Expr::Call(CallExpr {
                                    span: DUMMY_SP,
                                    callee: Callee::Expr(Box::new(Expr::Ident(Ident::new(
                                        "candid_none".into(),
                                        DUMMY_SP,
                                        SyntaxContext::empty(),
                                    )))),
                                    args: vec![],
                                    type_args: None,
                                    ctxt: SyntaxContext::empty(),
                                })),
                            })
                        }
                        _ => self._to_candid(&field_expr, &field.ty),
                    };

                    PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                        key,
                        value: Box::new(value),
                    })))
                })
                .collect(),
        })
    }

    fn convert_tuple_to_candid(&self, expr: &Expr, fields: &[Field]) -> Expr {
        // Create a new array with converted fields
        Expr::Array(ArrayLit {
            span: DUMMY_SP,
            elems: fields
                .iter()
                .enumerate()
                .map(|(i, field)| {
                    // Access tuple element by index
                    let elem_expr = Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(expr.clone()),
                        prop: MemberProp::Computed(ComputedPropName {
                            span: DUMMY_SP,
                            expr: Box::new(Expr::Lit(Lit::Num(Number {
                                span: DUMMY_SP,
                                value: i as f64,
                                raw: None,
                            }))),
                        }),
                    });

                    // Convert the tuple element
                    let value = self._to_candid(&elem_expr, &field.ty);

                    Some(ExprOrSpread {
                        spread: None,
                        expr: Box::new(value),
                    })
                })
                .collect(),
        })
    }

    fn convert_record_from_candid(&self, expr: &Expr, fields: &[Field]) -> Expr {
        // If the record is a tuple, handle differently
        if self.is_tuple(fields) {
            return self.convert_tuple_from_candid(expr, fields);
        }

        // Create a new object with converted fields
        Expr::Object(ObjectLit {
            span: DUMMY_SP,
            props: fields
                .iter()
                .map(|field| {
                    let key = match &*field.id {
                        Label::Named(name) => PropName::Ident(
                            Ident::new(name.clone().into(), DUMMY_SP, SyntaxContext::empty())
                                .into(),
                        ),
                        Label::Id(n) | Label::Unnamed(n) => PropName::Ident(
                            Ident::new(format!("_{}_", n).into(), DUMMY_SP, SyntaxContext::empty())
                                .into(),
                        ),
                    };

                    // Get the field from the input object
                    let field_expr = Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(expr.clone()),
                        prop: match &*field.id {
                            Label::Named(name) => MemberProp::Ident(
                                Ident::new(name.clone().into(), DUMMY_SP, SyntaxContext::empty())
                                    .into(),
                            ),
                            Label::Id(n) | Label::Unnamed(n) => MemberProp::Ident(
                                Ident::new(
                                    format!("_{}_", n).into(),
                                    DUMMY_SP,
                                    SyntaxContext::empty(),
                                )
                                .into(),
                            ),
                        },
                    });

                    // Convert the field value
                    let value = match field.ty.as_ref() {
                        TypeInner::Opt(_) => Expr::Call(CallExpr {
                            span: DUMMY_SP,
                            callee: Callee::Expr(Box::new(Expr::Ident(Ident::new(
                                "record_opt_to_undefined".into(),
                                DUMMY_SP,
                                SyntaxContext::empty(),
                            )))),
                            args: vec![ExprOrSpread {
                                spread: None,
                                expr: Box::new(self._from_candid(&field_expr, &field.ty)),
                            }],
                            type_args: None,
                            ctxt: SyntaxContext::empty(),
                        }),
                        _ => self._from_candid(&field_expr, &field.ty),
                    };

                    PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                        key,
                        value: Box::new(value),
                    })))
                })
                .collect(),
        })
    }

    fn convert_tuple_from_candid(&self, expr: &Expr, fields: &[Field]) -> Expr {
        // Create a new array with converted fields
        Expr::Array(ArrayLit {
            span: DUMMY_SP,
            elems: fields
                .iter()
                .enumerate()
                .map(|(i, field)| {
                    // Access tuple element by index
                    let elem_expr = Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(expr.clone()),
                        prop: MemberProp::Computed(ComputedPropName {
                            span: DUMMY_SP,
                            expr: Box::new(Expr::Lit(Lit::Num(Number {
                                span: DUMMY_SP,
                                value: i as f64,
                                raw: None,
                            }))),
                        }),
                    });

                    // Convert the tuple element
                    let value = self._from_candid(&elem_expr, &field.ty);

                    Some(ExprOrSpread {
                        spread: None,
                        expr: Box::new(value),
                    })
                })
                .collect(),
        })
    }

    fn convert_func_to_candid(&self, expr: &Expr, _func: &Function) -> Expr {
        // Functions are represented as Principals
        expr.clone() // Pass through as-is
    }

    fn convert_func_from_candid(&self, expr: &Expr, _func: &Function) -> Expr {
        // Functions are represented as Principals
        expr.clone() // Pass through as-is
    }

    fn convert_service_to_candid(&self, expr: &Expr) -> Expr {
        // Services are represented as Principals
        expr.clone() // Pass through as-is
    }

    fn convert_service_from_candid(&self, expr: &Expr) -> Expr {
        // Services are represented as Principals
        expr.clone() // Pass through as-is
    }

    fn convert_var_to_candid(&self, expr: &Expr, id: &str) -> Expr {
        // Look up the actual type and convert
        if let Ok(ty) = self.env.rec_find_type(id) {
            self._to_candid(expr, &ty)
        } else {
            // If type not found, pass through unchanged
            expr.clone()
        }
    }

    fn convert_var_from_candid(&self, expr: &Expr, id: &str) -> Expr {
        // Look up the actual type and convert
        if let Ok(ty) = self.env.rec_find_type(id) {
            self._from_candid(expr, &ty)
        } else {
            // If type not found, pass through unchanged
            expr.clone()
        }
    }

    // Helper to detect tuple types
    fn is_tuple(&self, fields: &[Field]) -> bool {
        fields
            .iter()
            .all(|f| matches!(&*f.id, Label::Id(_) | Label::Unnamed(_)))
    }
}

/// Extends TypeConverter to support handling multiple result values
pub fn convert_multi_return_from_candid(
    converter: &TypeConverter,
    expr: &Expr,
    types: &[Type],
) -> Expr {
    if types.len() == 0 {
        // No return value, return void
        return Expr::Lit(Lit::Null(Null { span: DUMMY_SP }));
    } else if types.len() == 1 {
        // Single return value
        return converter.from_candid(expr, &types[0]);
    } else {
        // Multiple return values in a tuple
        Expr::Array(ArrayLit {
            span: DUMMY_SP,
            elems: types
                .iter()
                .enumerate()
                .map(|(i, ty)| {
                    // Access return value by index
                    let elem_expr = Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(expr.clone()),
                        prop: MemberProp::Computed(ComputedPropName {
                            span: DUMMY_SP,
                            expr: Box::new(Expr::Lit(Lit::Num(Number {
                                span: DUMMY_SP,
                                value: i as f64,
                                raw: None,
                            }))),
                        }),
                    });

                    // Convert the return value
                    let value = converter.from_candid(&elem_expr, ty);

                    Some(ExprOrSpread {
                        spread: None,
                        expr: Box::new(value),
                    })
                })
                .collect(),
        })
    }
}
