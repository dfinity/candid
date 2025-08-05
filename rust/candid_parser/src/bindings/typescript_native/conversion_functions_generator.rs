use super::original_typescript_types::CandidTypesConverter;
use super::new_typescript_native_types::{convert_type, is_recursive_optional};
use super::utils::{contains_unicode_characters, get_ident_guarded};
use candid::types::{Field, Label, Type, TypeEnv, TypeInner};
use std::collections::{HashMap, HashSet};
use swc_core::common::{SyntaxContext, DUMMY_SP};
use swc_core::ecma::ast::*;
/// Provides functions to generate JavaScript expressions that convert
/// between TypeScript and Candid representations using a function-based approach.
pub struct TypeConverter<'a> {
    env: &'a TypeEnv,
    // Track function names by type
    to_candid_functions: HashMap<Type, String>,
    from_candid_functions: HashMap<Type, String>,
    // Track which types have fully generated functions
    to_candid_generated: HashSet<Type>,
    from_candid_generated: HashSet<Type>,
    // Store all generated function declarations
    generated_functions: HashMap<String, Stmt>,
    // Track types being processed to detect recursion
    processing_to_candid: HashSet<Type>,
    processing_from_candid: HashSet<Type>,
    processing_conversion: HashSet<Type>,
    // Counter for unique function names
    function_counter: usize,
    candid_types_converter: CandidTypesConverter<'a>,
    enum_declarations: &'a mut HashMap<Vec<Field>, (TsEnumDecl, String)>,
}

impl<'a> TypeConverter<'a> {
    /// Create a new TypeConverter with the given type environment
    pub fn new(
        env: &'a TypeEnv,
        enum_declarations: &'a mut HashMap<Vec<Field>, (TsEnumDecl, String)>,
    ) -> Self {
        TypeConverter {
            env,
            to_candid_functions: HashMap::new(),
            from_candid_functions: HashMap::new(),
            to_candid_generated: HashSet::new(),
            from_candid_generated: HashSet::new(),
            generated_functions: HashMap::new(),
            processing_to_candid: HashSet::new(),
            processing_from_candid: HashSet::new(),
            processing_conversion: HashSet::new(),
            function_counter: 0,
            candid_types_converter: CandidTypesConverter::new(env),
            enum_declarations,
        }
    }

    /// Get all generated function declarations
    pub fn get_generated_functions(&self) -> Vec<Stmt> {
        self.generated_functions.values().cloned().collect()
    }

    /// Get mutable access to enum_declarations
    pub fn enum_declarations_mut(&mut self) -> &mut HashMap<Vec<Field>, (TsEnumDecl, String)> {
        self.enum_declarations
    }

    /// Check if a type requires conversion or can be passed through directly
    fn needs_conversion(&mut self, ty: &Type) -> bool {
        // Check if we already computed this type
        let is_recursive = self.processing_conversion.contains(ty);

        self.processing_conversion.insert(ty.clone());

        if is_recursive {
            return true;
        }

        let result = match ty.as_ref() {
            // Types that don't need conversion
            TypeInner::Null => false,
            TypeInner::Bool => false,
            TypeInner::Text => false,
            TypeInner::Nat8 => false,
            TypeInner::Nat16 => false,
            TypeInner::Nat32 => false,
            TypeInner::Int8 => false,
            TypeInner::Int16 => false,
            TypeInner::Int32 => false,
            TypeInner::Float32 => false,
            TypeInner::Float64 => false,
            TypeInner::Reserved => false,

            TypeInner::Nat => false,
            TypeInner::Int => false,
            TypeInner::Nat64 => false,
            TypeInner::Int64 => false,
            TypeInner::Principal => false,
            TypeInner::Empty => false,

            // Types that always need conversion
            TypeInner::Opt(_) => true,
            // Container types - need conversion only if their contents need conversion
            TypeInner::Vec(inner) => self.needs_conversion(inner),
            TypeInner::Record(fields) => {
                // Only needs conversion if any field needs conversion
                fields.iter().any(|field| self.needs_conversion(&field.ty))
            }
            TypeInner::Variant(_) => true,
            TypeInner::Var(id) => {
                // Check if the named type needs conversion
                if let Ok(actual_ty) = self.env.rec_find_type(id) {
                    self.needs_conversion(actual_ty)
                } else {
                    true // Conservative default
                }
            }
            TypeInner::Func(_) => false,
            TypeInner::Service(_) => false,
            _ => true, // Conservative default - convert if unsure
        };
        self.processing_conversion.remove(ty);
        result
    }

    /// Get the function name for converting from TypeScript to Candid
    fn get_to_candid_function_name(&mut self, ty: &Type) -> String {
        if let Some(name) = self.to_candid_functions.get(ty) {
            return name.clone();
        }

        // Generate a base name for the function
        let base_name = match ty.as_ref() {
            TypeInner::Var(id) => format!("to_candid_{}", id),
            _ => {
                // For anonymous types, use a descriptive prefix based on the type
                let type_prefix = match ty.as_ref() {
                    TypeInner::Null => "null",
                    TypeInner::Bool => "bool",
                    TypeInner::Nat => "nat",
                    TypeInner::Int => "int",
                    TypeInner::Nat8 => "nat8",
                    TypeInner::Nat16 => "nat16",
                    TypeInner::Nat32 => "nat32",
                    TypeInner::Nat64 => "nat64",
                    TypeInner::Int8 => "int8",
                    TypeInner::Int16 => "int16",
                    TypeInner::Int32 => "int32",
                    TypeInner::Int64 => "int64",
                    TypeInner::Float32 => "float32",
                    TypeInner::Float64 => "float64",
                    TypeInner::Text => "text",
                    TypeInner::Reserved => "reserved",
                    TypeInner::Empty => "empty",
                    TypeInner::Principal => "principal",
                    TypeInner::Opt(_) => "opt",
                    TypeInner::Vec(_) => "vec",
                    TypeInner::Record(fields) => {
                        if self.is_tuple(fields) {
                            "tuple"
                        } else {
                            "record"
                        }
                    }
                    TypeInner::Variant(_) => "variant",
                    TypeInner::Func(_) => "func",
                    TypeInner::Service(_) => "service",
                    _ => "anonymous",
                };
                format!("to_candid_{}", type_prefix)
            }
        };

        // Generate a unique name with counter
        self.function_counter += 1;
        let name = format!("{}_n{}", base_name, self.function_counter);

        self.to_candid_functions.insert(ty.clone(), name.clone());
        name
    }

    /// Get the function name for converting from Candid to TypeScript
    fn get_from_candid_function_name(&mut self, ty: &Type) -> String {
        if let Some(name) = self.from_candid_functions.get(ty) {
            return name.clone();
        }

        // Generate a base name for the function
        let base_name = match ty.as_ref() {
            TypeInner::Var(id) => format!("from_candid_{}", id),
            _ => {
                // For anonymous types, use a descriptive prefix based on the type
                let type_prefix = match ty.as_ref() {
                    TypeInner::Null => "null",
                    TypeInner::Bool => "bool",
                    TypeInner::Nat => "nat",
                    TypeInner::Int => "int",
                    TypeInner::Nat8 => "nat8",
                    TypeInner::Nat16 => "nat16",
                    TypeInner::Nat32 => "nat32",
                    TypeInner::Nat64 => "nat64",
                    TypeInner::Int8 => "int8",
                    TypeInner::Int16 => "int16",
                    TypeInner::Int32 => "int32",
                    TypeInner::Int64 => "int64",
                    TypeInner::Float32 => "float32",
                    TypeInner::Float64 => "float64",
                    TypeInner::Text => "text",
                    TypeInner::Reserved => "reserved",
                    TypeInner::Empty => "empty",
                    TypeInner::Principal => "principal",
                    TypeInner::Opt(_) => "opt",
                    TypeInner::Vec(_) => "vec",
                    TypeInner::Record(fields) => {
                        if self.is_tuple(fields) {
                            "tuple"
                        } else {
                            "record"
                        }
                    }
                    TypeInner::Variant(_) => "variant",
                    TypeInner::Func(_) => "func",
                    TypeInner::Service(_) => "service",
                    _ => "anonymous",
                };
                format!("from_candid_{}", type_prefix)
            }
        };

        // Generate a unique name with counter
        self.function_counter += 1;
        let name = format!("{}_n{}", base_name, self.function_counter);

        self.from_candid_functions.insert(ty.clone(), name.clone());
        name
    }

    /// Create an identifier expression
    fn create_ident(&self, name: &str) -> Expr {
        Expr::Ident(Ident::new(name.into(), DUMMY_SP, SyntaxContext::empty()))
    }

    /// Create a function call expression
    fn create_call(&self, callee: &str, args: Vec<ExprOrSpread>) -> Expr {
        Expr::Call(CallExpr {
            span: DUMMY_SP,
            callee: Callee::Expr(Box::new(self.create_ident(callee))),
            args,
            type_args: None,
            ctxt: SyntaxContext::empty(),
        })
    }

    /// Create a function call argument
    fn create_arg(&self, expr: Expr) -> ExprOrSpread {
        ExprOrSpread {
            spread: None,
            expr: Box::new(expr),
        }
    }

    /// Generate the body of a TypeScript -> Candid conversion function
    fn generate_to_candid_body(&mut self, ty: &Type, param_name: &str) -> Expr {
        match ty.as_ref() {
            TypeInner::Null => self.create_ident(param_name),
            TypeInner::Bool => self.create_ident(param_name),
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
            | TypeInner::Float64 => self.create_ident(param_name),
            TypeInner::Text => self.create_ident(param_name),
            TypeInner::Reserved => self.create_ident(param_name),
            TypeInner::Empty => {
                // Empty type is represented as null in JavaScript
                Expr::Lit(Lit::Null(Null { span: DUMMY_SP }))
            }
            TypeInner::Principal => self.convert_principal_to_candid_body(param_name),
            TypeInner::Opt(ref inner) => self.convert_opt_to_candid_body(inner, param_name),
            TypeInner::Vec(ref inner) => self.convert_vec_to_candid_body(inner, param_name),
            TypeInner::Record(ref fields) => self.convert_record_to_candid_body(fields, param_name),
            TypeInner::Variant(ref fields) => {
                self.convert_variant_to_candid_body(fields, param_name)
            }
            TypeInner::Func(ref func) => self.convert_func_to_candid_body(func, param_name),
            TypeInner::Service(_) => self.create_ident(param_name), // Pass through as-is
            TypeInner::Var(ref id) => {
                // For named types, delegate to another conversion function
                if let Ok(actual_ty) = self.env.rec_find_type(id) {
                    // If the actual type doesn't need conversion, return the expression directly
                    if !self.needs_conversion(actual_ty) {
                        return self.create_ident(param_name);
                    }

                    // Generate the function for the actual type if needed
                    let inner_function_name = self.get_to_candid_function_name(actual_ty);
                    self.generate_to_candid_function(actual_ty, &inner_function_name);

                    // Return a call to that function
                    self.create_call(
                        &inner_function_name,
                        vec![self.create_arg(self.create_ident(param_name))],
                    )
                } else {
                    // If type not found, pass through unchanged
                    self.create_ident(param_name)
                }
            }
            // For unsupported types, we pass through unchanged
            _ => self.create_ident(param_name),
        }
    }

    // --- Type-specific conversion methods (TypeScript -> Candid) ---

    fn convert_principal_to_candid_body(&mut self, param_name: &str) -> Expr {
        // Principal objects are already compatible
        self.create_ident(param_name)
    }

    fn convert_opt_to_candid_body(&mut self, inner: &Type, param_name: &str) -> Expr {
        // For nested options, we need to handle them recursively
        if let TypeInner::Opt(_) = inner.as_ref() {
            // Generate a conversion function for the inner option type
            let inner_function_name = self.get_to_candid_function_name(inner);
            self.generate_to_candid_function(inner, &inner_function_name);

            // Create expression: isNone(value) ? candid_none() : candid_some(inner_fn(unwrap(value)))
            return Expr::Cond(CondExpr {
                span: DUMMY_SP,
                test: Box::new(Expr::Call(CallExpr {
                    span: DUMMY_SP,
                    callee: Callee::Expr(Box::new(self.create_ident("isNone"))),
                    args: vec![self.create_arg(self.create_ident(param_name))],
                    type_args: None,
                    ctxt: SyntaxContext::empty(),
                })),
                cons: Box::new(self.create_call("candid_none", vec![])),
                alt: Box::new(self.create_call(
                    "candid_some",
                    vec![self.create_arg(self.create_call(
                        &inner_function_name,
                        vec![self.create_arg(self.create_call(
                            "unwrap",
                            vec![self.create_arg(self.create_ident(param_name))],
                        ))],
                    ))],
                )),
            });
        }

        // Check for recursive option types (Some<T> | None pattern)
        if let TypeInner::Var(id) = inner.as_ref() {
            if let Ok(inner_type) = self.env.find_type(id) {
                let mut visited = std::collections::HashSet::new();
                let is_recursive = is_recursive_optional(self.env, inner_type, &mut visited);

                if is_recursive {
                    // For recursive patterns using Some/None, check for _tag property
                    // Generate conversion function for the inner type
                    let inner_function_name = self.get_to_candid_function_name(inner);
                    self.generate_to_candid_function(inner, &inner_function_name);

                    return Expr::Cond(CondExpr {
                        span: DUMMY_SP,
                        test: Box::new(Expr::Bin(BinExpr {
                            span: DUMMY_SP,
                            op: BinaryOp::EqEqEq,
                            left: Box::new(Expr::Member(MemberExpr {
                                span: DUMMY_SP,
                                obj: Box::new(self.create_ident(param_name)),
                                prop: MemberProp::Ident(
                                    Ident::new("_tag".into(), DUMMY_SP, SyntaxContext::empty())
                                        .into(),
                                ),
                            })),
                            right: Box::new(Expr::Lit(Lit::Str(Str {
                                span: DUMMY_SP,
                                value: "None".into(),
                                raw: None,
                            }))),
                        })),
                        cons: Box::new(self.create_call("candid_none", vec![])),
                        alt: Box::new(self.create_call(
                            "candid_some",
                            vec![self.create_arg(self.create_call(
                                &inner_function_name,
                                vec![self.create_arg(Expr::Member(MemberExpr {
                                    span: DUMMY_SP,
                                    obj: Box::new(self.create_ident(param_name)),
                                    prop: MemberProp::Ident(
                                        Ident::new(
                                            "value".into(),
                                            DUMMY_SP,
                                            SyntaxContext::empty(),
                                        )
                                        .into(),
                                    ),
                                }))],
                            ))],
                        )),
                    });
                }
            }
        }

        // For inner types that don't need conversion, we can simplify
        if !self.needs_conversion(inner) {
            return Expr::Cond(CondExpr {
                span: DUMMY_SP,
                test: Box::new(Expr::Bin(BinExpr {
                    span: DUMMY_SP,
                    op: BinaryOp::EqEqEq,
                    left: Box::new(self.create_ident(param_name)),
                    right: Box::new(Expr::Lit(Lit::Null(Null { span: DUMMY_SP }))),
                })),
                cons: Box::new(self.create_call("candid_none", vec![])),
                alt: Box::new(self.create_call(
                    "candid_some",
                    vec![self.create_arg(self.create_ident(param_name))],
                )),
            });
        }

        // Only for non-option inner types that need conversion,
        // generate a specific conversion function
        let inner_function_name = self.get_to_candid_function_name(inner);
        self.generate_to_candid_function(inner, &inner_function_name);

        // value === null ? candid_none() : candid_some(to_candid_inner(value))
        Expr::Cond(CondExpr {
            span: DUMMY_SP,
            test: Box::new(Expr::Bin(BinExpr {
                span: DUMMY_SP,
                op: BinaryOp::EqEqEq,
                left: Box::new(self.create_ident(param_name)),
                right: Box::new(Expr::Lit(Lit::Null(Null { span: DUMMY_SP }))),
            })),
            cons: Box::new(self.create_call("candid_none", vec![])),
            alt: Box::new(self.create_call(
                "candid_some",
                vec![self.create_arg(self.create_call(
                    &inner_function_name,
                    vec![self.create_arg(self.create_ident(param_name))],
                ))],
            )),
        })
    }

    fn convert_vec_to_candid_body(&mut self, inner: &Type, param_name: &str) -> Expr {
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
                // For numeric types, we can just pass through or convert to typed array
                self.create_ident(param_name)
            }
            _ => {
                // Optimization for inner types that don't need conversion
                if !self.needs_conversion(inner) {
                    return self.create_ident(param_name);
                }

                // Get conversion function for inner type
                let inner_function_name = self.get_to_candid_function_name(inner);
                self.generate_to_candid_function(inner, &inner_function_name);

                // value.map(x => to_candid_inner(x))
                Expr::Call(CallExpr {
                    span: DUMMY_SP,
                    callee: Callee::Expr(Box::new(Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(self.create_ident(param_name)),
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
                            body: Box::new(BlockStmtOrExpr::Expr(Box::new(self.create_call(
                                &inner_function_name,
                                vec![self.create_arg(self.create_ident("x"))],
                            )))),
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

    fn convert_record_to_candid_body(&mut self, fields: &[Field], param_name: &str) -> Expr {
        // If the record is a tuple, handle differently
        if self.is_tuple(fields) {
            return self.convert_tuple_to_candid_body(fields, param_name);
        }

        // Create a new object with converted fields
        Expr::Object(ObjectLit {
            span: DUMMY_SP,
            props: fields
                .iter()
                .map(|field| {
                    let field_name = match &*field.id {
                        Label::Named(name) => name.clone(),
                        Label::Id(n) | Label::Unnamed(n) => format!("_{}_", n),
                    };

                    // Get the field from the input object
                    let field_access = Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(self.create_ident(param_name)),
                        prop: MemberProp::Ident(
                            Ident::new(field_name.clone().into(), DUMMY_SP, SyntaxContext::empty())
                                .into(),
                        ),
                    });

                    let prop_name = PropName::Ident(
                        Ident::new(field_name.into(), DUMMY_SP, SyntaxContext::empty()).into(),
                    );

                    // Convert the field value based on its type
                    let value = match field.ty.as_ref() {
                        TypeInner::Opt(inner) => {
                            // For optional fields, handle undefined/null specially
                            if !self.needs_conversion(inner) {
                                Expr::Cond(CondExpr {
                                    span: DUMMY_SP,
                                    test: Box::new(field_access.clone()),
                                    cons: Box::new(self.create_call(
                                        "candid_some",
                                        vec![self.create_arg(field_access.clone())],
                                    )),
                                    alt: Box::new(self.create_call("candid_none", vec![])),
                                })
                            } else {
                                let inner_function_name = self.get_to_candid_function_name(inner);
                                self.generate_to_candid_function(inner, &inner_function_name);

                                Expr::Cond(CondExpr {
                                    span: DUMMY_SP,
                                    test: Box::new(field_access.clone()),
                                    cons: Box::new(self.create_call(
                                        "candid_some",
                                        vec![self.create_arg(self.create_call(
                                            &inner_function_name,
                                            vec![self.create_arg(field_access.clone())],
                                        ))],
                                    )),
                                    alt: Box::new(self.create_call("candid_none", vec![])),
                                })
                            }
                        }
                        _ => {
                            // For normal fields, check if conversion is needed
                            if !self.needs_conversion(&field.ty) {
                                field_access
                            } else {
                                // Convert the value using appropriate function
                                let function_name = self.get_to_candid_function_name(&field.ty);
                                self.generate_to_candid_function(&field.ty, &function_name);
                                self.create_call(
                                    &function_name,
                                    vec![self.create_arg(field_access)],
                                )
                            }
                        }
                    };

                    PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                        key: prop_name,
                        value: Box::new(value),
                    })))
                })
                .collect(),
        })
    }

    fn convert_tuple_to_candid_body(&mut self, fields: &[Field], param_name: &str) -> Expr {
        // Create a new array with converted fields
        Expr::Array(ArrayLit {
            span: DUMMY_SP,
            elems: fields
                .iter()
                .enumerate()
                .map(|(i, field)| {
                    // Access tuple element by index
                    let elem_access = Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(self.create_ident(param_name)),
                        prop: MemberProp::Computed(ComputedPropName {
                            span: DUMMY_SP,
                            expr: Box::new(Expr::Lit(Lit::Num(Number {
                                span: DUMMY_SP,
                                value: i as f64,
                                raw: None,
                            }))),
                        }),
                    });

                    // Check if conversion is needed
                    let value = if !self.needs_conversion(&field.ty) {
                        elem_access
                    } else {
                        // Convert the tuple element
                        let function_name = self.get_to_candid_function_name(&field.ty);
                        self.generate_to_candid_function(&field.ty, &function_name);
                        self.create_call(&function_name, vec![self.create_arg(elem_access)])
                    };

                    Some(ExprOrSpread {
                        spread: None,
                        expr: Box::new(value),
                    })
                })
                .collect(),
        })
    }

    fn convert_variant_to_candid_body(&mut self, fields: &[Field], param_name: &str) -> Expr {
        // If there are no fields, return the input unchanged
        if fields.is_empty() {
            return self.create_ident(param_name);
        }

        // Check if all variants have the same type (especially null)
        let all_null = fields
            .iter()
            .all(|f| matches!(f.ty.as_ref(), TypeInner::Null));
        if all_null {
            // For enums, compare against enum members
            let enum_name = self
                .enum_declarations
                .get(&fields.to_vec())
                .unwrap()
                .1
                .clone();

            let mut result = self.create_ident(param_name); // Default fallback

            // Process all fields in reverse order to build the chain
            for field in fields.iter().rev() {
                let field_name = match &*field.id {
                    Label::Named(name) => name.clone(),
                    Label::Id(n) | Label::Unnamed(n) => format!("_{}_", n),
                };

                let enum_member = if contains_unicode_characters(&field_name) {
                    Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(self.create_ident(&enum_name)),
                        prop: MemberProp::Computed(ComputedPropName {
                            span: DUMMY_SP,
                            expr: Box::new(Expr::Lit(Lit::Str(Str {
                                span: DUMMY_SP,
                                value: field_name.clone().into(),
                                raw: None,
                            }))),
                        }),
                    })
                } else {
                    Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(self.create_ident(&enum_name)),
                        prop: MemberProp::Ident(
                            Ident::new(field_name.clone().into(), DUMMY_SP, SyntaxContext::empty())
                                .into(),
                        ),
                    })
                };

                let condition = Expr::Bin(BinExpr {
                    span: DUMMY_SP,
                    op: BinaryOp::EqEq,
                    left: Box::new(self.create_ident(param_name)),
                    right: Box::new(enum_member),
                });

                // Create result: { field_name: null }
                let field_result = Expr::Object(ObjectLit {
                    span: DUMMY_SP,
                    props: vec![PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                        key: PropName::Ident(get_ident_guarded(&field_name).into()),
                        value: Box::new(Expr::Lit(Lit::Null(Null { span: DUMMY_SP }))),
                    })))],
                });

                // Create a new conditional with this field's condition and result,
                // with the previous result as the alternate
                result = Expr::Cond(CondExpr {
                    span: DUMMY_SP,
                    test: Box::new(condition),
                    cons: Box::new(field_result),
                    alt: Box::new(result),
                });
            }

            result
        } else {
            // For variants with different types, check for _tag property
            // This is for TypeScript unions of object types: { tag1: value1 } | { tag2: value2 }

            // Build a series of conditions to check each tag
            let mut result = self.create_ident(param_name); // Default fallback

            for field in fields.iter().rev() {
                let field_name = match &*field.id {
                    Label::Named(name) => name.clone(),
                    Label::Id(n) | Label::Unnamed(n) => format!("_{}_", n),
                };

                // Check if this variant field exists on the object using: field in value
                let condition = Expr::Bin(BinExpr {
                    span: DUMMY_SP,
                    op: BinaryOp::In,
                    left: Box::new(Expr::Lit(Lit::Str(Str {
                        span: DUMMY_SP,
                        value: field_name.clone().into(),
                        raw: None,
                    }))),
                    right: Box::new(self.create_ident(param_name)),
                });

                // Create result: { field_name: field_value }
                // Use a clone of field_name to avoid the "use after move" error

                let field_access = Expr::Member(MemberExpr {
                    span: DUMMY_SP,
                    obj: Box::new(self.create_ident(param_name)),
                    prop: MemberProp::Ident(
                        Ident::new(field_name.clone().into(), DUMMY_SP, SyntaxContext::empty())
                            .into(),
                    ),
                });

                let field_result = match field.ty.as_ref() {
                    TypeInner::Opt(inner) => {
                        // For optional fields, handle undefined/null specially
                        if !self.needs_conversion(inner) {
                            Expr::Cond(CondExpr {
                                span: DUMMY_SP,
                                test: Box::new(field_access.clone()),
                                cons: Box::new(self.create_call(
                                    "candid_some",
                                    vec![self.create_arg(field_access.clone())],
                                )),
                                alt: Box::new(self.create_call("candid_none", vec![])),
                            })
                        } else {
                            let inner_function_name = self.get_to_candid_function_name(inner);
                            self.generate_to_candid_function(inner, &inner_function_name);

                            Expr::Cond(CondExpr {
                                span: DUMMY_SP,
                                test: Box::new(field_access.clone()),
                                cons: Box::new(self.create_call(
                                    "candid_some",
                                    vec![self.create_arg(self.create_call(
                                        &inner_function_name,
                                        vec![self.create_arg(field_access.clone())],
                                    ))],
                                )),
                                alt: Box::new(self.create_call("candid_none", vec![])),
                            })
                        }
                    }
                    _ => {
                        // For normal fields, check if conversion is needed
                        if !self.needs_conversion(&field.ty) {
                            field_access
                        } else {
                            let inner_function_name = self.get_to_candid_function_name(&field.ty);
                            self.generate_to_candid_function(&field.ty, &inner_function_name);
                            // Convert the value using appropriate function
                            self.create_call(
                                &inner_function_name,
                                vec![self.create_arg(field_access.clone())],
                            )
                        }
                    }
                };

                // Create a new conditional with this field's condition and result
                result = Expr::Cond(CondExpr {
                    span: DUMMY_SP,
                    test: Box::new(condition),
                    cons: Box::new(Expr::Object(ObjectLit {
                        span: DUMMY_SP,
                        props: vec![PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                            key: PropName::Ident(
                                Ident::new(field_name.into(), DUMMY_SP, SyntaxContext::empty())
                                    .into(),
                            ),
                            value: Box::new(field_result),
                        })))],
                    })),
                    alt: Box::new(result),
                });
            }

            result
        }
    }
    fn convert_func_to_candid_body(
        &mut self,
        _func: &candid::types::Function,
        param_name: &str,
    ) -> Expr {
        // Functions are represented as Principals
        self.create_ident(param_name)
    }

    // --- Type-specific conversion methods (Candid -> TypeScript) ---

    /// Generate an expression that converts from Candid to TypeScript representation
    /// for the given Candid type and expression.
    pub fn convert_from_candid(&mut self, expr: &Expr, ty: &Type) -> Expr {
        // For simple types that don't need conversion, return the expression directly
        if !self.needs_conversion(ty) {
            return expr.clone();
        }

        let function_name = self.get_from_candid_function_name(ty);

        // Generate the function if it doesn't exist
        self.generate_from_candid_function(ty, &function_name);

        // Return a call to the function
        self.create_call(&function_name, vec![self.create_arg(expr.clone())])
    }

    /// Generate a function that converts from Candid to TypeScript
    fn generate_from_candid_function(&mut self, ty: &Type, function_name: &str) {
        // Skip if function already generated for this type
        if self.from_candid_generated.contains(ty) {
            return;
        }

        // Check for recursion
        let is_recursive = self.processing_from_candid.contains(ty);

        // Add to processing set to detect recursion
        self.processing_from_candid.insert(ty.clone());

        // Generate parameter type annotation (Candid type)
        let param_name = "value";
        let param_type_ann = self.candid_types_converter.get_candid_type(ty);

        // Generate return type annotation (TypeScript type)
        let return_type_ann = self.create_ts_type_annotation(ty);

        // Generate function body
        let body_expr = if is_recursive {
            // For recursive types, return a placeholder initially
            self.create_ident(param_name)
        } else {
            self.generate_from_candid_body(ty, param_name)
        };

        // Create function declaration with type annotations
        let fn_decl = Stmt::Decl(Decl::Fn(FnDecl {
            ident: Ident::new(function_name.into(), DUMMY_SP, SyntaxContext::empty()),
            declare: false,
            function: Box::new(swc_core::ecma::ast::Function {
                params: vec![Param {
                    span: DUMMY_SP,
                    decorators: vec![],
                    pat: Pat::Ident(BindingIdent {
                        id: Ident::new(param_name.into(), DUMMY_SP, SyntaxContext::empty()),
                        type_ann: Some(Box::new(TsTypeAnn {
                            span: DUMMY_SP,
                            type_ann: Box::new(param_type_ann),
                        })),
                    }),
                }],
                decorators: vec![],
                span: DUMMY_SP,
                body: Some(BlockStmt {
                    span: DUMMY_SP,
                    stmts: vec![Stmt::Return(ReturnStmt {
                        span: DUMMY_SP,
                        arg: Some(Box::new(body_expr)),
                    })],
                    ctxt: SyntaxContext::empty(),
                }),
                is_generator: false,
                is_async: false,
                type_params: None,
                return_type: Some(Box::new(TsTypeAnn {
                    span: DUMMY_SP,
                    type_ann: Box::new(return_type_ann),
                })),
                ctxt: SyntaxContext::empty(),
            }),
        }));

        // Add function to generated list
        self.generated_functions
            .insert(function_name.into(), fn_decl);

        // Mark this type as fully generated
        self.from_candid_generated.insert(ty.clone());

        // If recursive, update the function body now that the function exists
        if is_recursive {
            let body_expr = self.generate_from_candid_body(ty, param_name);
            if let Some(Stmt::Decl(Decl::Fn(fn_decl))) =
                self.generated_functions.get_mut(function_name)
            {
                if let Some(BlockStmt { stmts, .. }) = &mut fn_decl.function.body {
                    if let Some(Stmt::Return(ret)) = stmts.last_mut() {
                        ret.arg = Some(Box::new(body_expr));
                    }
                }
            }
        }

        // Remove from processing set
        self.processing_from_candid.remove(ty);
    }

    /// Create a TypeScript type annotation for a given Candid type
    fn create_ts_type_annotation(&mut self, ty: &Type) -> TsType {
        convert_type(self.enum_declarations, self.env, ty, true)
    }

    fn generate_from_candid_body(&mut self, ty: &Type, param_name: &str) -> Expr {
        match ty.as_ref() {
            TypeInner::Null => self.create_ident(param_name),
            TypeInner::Bool => self.create_ident(param_name),
            TypeInner::Nat | TypeInner::Int | TypeInner::Nat64 | TypeInner::Int64 => {
                self.convert_from_bigint_body(param_name)
            }
            TypeInner::Nat8
            | TypeInner::Nat16
            | TypeInner::Nat32
            | TypeInner::Int8
            | TypeInner::Int16
            | TypeInner::Int32
            | TypeInner::Float32
            | TypeInner::Float64 => self.create_ident(param_name),
            TypeInner::Text => self.create_ident(param_name),
            TypeInner::Reserved => self.create_ident(param_name),
            TypeInner::Empty => {
                // Empty type is represented as null in JavaScript
                Expr::Lit(Lit::Null(Null { span: DUMMY_SP }))
            }
            TypeInner::Principal => self.convert_principal_from_candid_body(param_name),
            TypeInner::Opt(ref inner) => self.convert_opt_from_candid_body(inner, param_name),
            TypeInner::Vec(ref inner) => self.convert_vec_from_candid_body(inner, param_name),
            TypeInner::Record(ref fields) => {
                self.convert_record_from_candid_body(fields, param_name)
            }
            TypeInner::Variant(ref fields) => {
                self.convert_variant_from_candid_body(fields, param_name)
            }
            TypeInner::Func(ref func) => self.convert_func_from_candid_body(func, param_name),
            TypeInner::Service(_) => self.create_ident(param_name), // Pass through as-is
            TypeInner::Var(ref id) => {
                // For named types, delegate to another conversion function
                if let Ok(actual_ty) = self.env.rec_find_type(id) {
                    // If the actual type doesn't need conversion, return directly
                    if !self.needs_conversion(actual_ty) {
                        return self.create_ident(param_name);
                    }

                    // Generate the function for the actual type if needed
                    let inner_function_name = self.get_from_candid_function_name(actual_ty);
                    self.generate_from_candid_function(actual_ty, &inner_function_name);

                    // Return a call to that function
                    self.create_call(
                        &inner_function_name,
                        vec![self.create_arg(self.create_ident(param_name))],
                    )
                } else {
                    // If type not found, pass through unchanged
                    self.create_ident(param_name)
                }
            }
            // For unsupported types, we pass through unchanged
            _ => self.create_ident(param_name),
        }
    }

    fn convert_from_bigint_body(&mut self, param_name: &str) -> Expr {
        // For now, just pass through bigints
        self.create_ident(param_name)
    }

    fn convert_principal_from_candid_body(&mut self, param_name: &str) -> Expr {
        // Principal objects are already compatible
        self.create_ident(param_name)
    }

    fn convert_opt_from_candid_body(&mut self, inner: &Type, param_name: &str) -> Expr {
        // Check for recursive option types (Some<T> | None pattern)
        if let TypeInner::Var(id) = inner.as_ref() {
            if let Ok(inner_type) = self.env.find_type(id) {
                let mut visited = std::collections::HashSet::new();
                let is_recursive = is_recursive_optional(self.env, inner_type, &mut visited);

                if is_recursive {
                    // Get or create a reference to the inner type conversion function
                    let inner_function_name = self.get_from_candid_function_name(inner);
                    self.generate_from_candid_function(inner, &inner_function_name);

                    // For recursive options, convert from [] | [value] to Some/None
                    return Expr::Cond(CondExpr {
                        span: DUMMY_SP,
                        test: Box::new(Expr::Bin(BinExpr {
                            span: DUMMY_SP,
                            op: BinaryOp::EqEqEq,
                            left: Box::new(Expr::Member(MemberExpr {
                                span: DUMMY_SP,
                                obj: Box::new(self.create_ident(param_name)),
                                prop: MemberProp::Ident(
                                    Ident::new("length".into(), DUMMY_SP, SyntaxContext::empty())
                                        .into(),
                                ),
                            })),
                            right: Box::new(Expr::Lit(Lit::Num(Number {
                                span: DUMMY_SP,
                                value: 0.0,
                                raw: None,
                            }))),
                        })),
                        // Return None for empty array
                        cons: Box::new(self.create_call("none", vec![])),
                        // Return Some for non-empty array with recursive conversion
                        alt: Box::new(self.create_call(
                            "some",
                            vec![self.create_arg(self.create_call(
                                &inner_function_name,
                                vec![self.create_arg(Expr::Member(MemberExpr {
                                    span: DUMMY_SP,
                                    obj: Box::new(self.create_ident(param_name)),
                                    prop: MemberProp::Computed(ComputedPropName {
                                        span: DUMMY_SP,
                                        expr: Box::new(Expr::Lit(Lit::Num(Number {
                                            span: DUMMY_SP,
                                            value: 0.0,
                                            raw: None,
                                        }))),
                                    }),
                                }))],
                            ))],
                        )),
                    });
                }
            }
        }

        // For inner types that don't need conversion, optimize
        if !self.needs_conversion(inner) {
            return Expr::Cond(CondExpr {
                span: DUMMY_SP,
                test: Box::new(Expr::Bin(BinExpr {
                    span: DUMMY_SP,
                    op: BinaryOp::EqEqEq,
                    left: Box::new(Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(self.create_ident(param_name)),
                        prop: MemberProp::Ident(
                            Ident::new("length".into(), DUMMY_SP, SyntaxContext::empty()).into(),
                        ),
                    })),
                    right: Box::new(Expr::Lit(Lit::Num(Number {
                        span: DUMMY_SP,
                        value: 0.0,
                        raw: None,
                    }))),
                })),
                cons: Box::new(Expr::Lit(Lit::Null(Null { span: DUMMY_SP }))),
                alt: Box::new(Expr::Member(MemberExpr {
                    span: DUMMY_SP,
                    obj: Box::new(self.create_ident(param_name)),
                    prop: MemberProp::Computed(ComputedPropName {
                        span: DUMMY_SP,
                        expr: Box::new(Expr::Lit(Lit::Num(Number {
                            span: DUMMY_SP,
                            value: 0.0,
                            raw: None,
                        }))),
                    }),
                })),
            });
        }

        // Get conversion function for inner type
        let inner_function_name = self.get_from_candid_function_name(inner);
        self.generate_from_candid_function(inner, &inner_function_name);

        match &inner.as_ref() {
            // Types that don't need conversion
            TypeInner::Opt(_) => Expr::Cond(CondExpr {
                span: DUMMY_SP,
                test: Box::new(Expr::Bin(BinExpr {
                    span: DUMMY_SP,
                    op: BinaryOp::EqEqEq,
                    left: Box::new(Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(self.create_ident(param_name)),
                        prop: MemberProp::Ident(
                            Ident::new("length".into(), DUMMY_SP, SyntaxContext::empty()).into(),
                        ),
                    })),
                    right: Box::new(Expr::Lit(Lit::Num(Number {
                        span: DUMMY_SP,
                        value: 0.0,
                        raw: None,
                    }))),
                })),
                // Use null
                cons: Box::new(self.create_call("none", vec![])),
                // Wrap with some()
                alt: Box::new(self.create_call(
                    "some",
                    vec![self.create_arg(self.create_call(
                        &inner_function_name,
                        vec![self.create_arg(Expr::Member(MemberExpr {
                            span: DUMMY_SP,
                            obj: Box::new(self.create_ident(param_name)),
                            prop: MemberProp::Computed(ComputedPropName {
                                span: DUMMY_SP,
                                expr: Box::new(Expr::Lit(Lit::Num(Number {
                                    span: DUMMY_SP,
                                    value: 0.0,
                                    raw: None,
                                }))),
                            }),
                        }))],
                    ))],
                )),
            }),
            _ => Expr::Cond(CondExpr {
                span: DUMMY_SP,
                test: Box::new(Expr::Bin(BinExpr {
                    span: DUMMY_SP,
                    op: BinaryOp::EqEqEq,
                    left: Box::new(Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(self.create_ident(param_name)),
                        prop: MemberProp::Ident(
                            Ident::new("length".into(), DUMMY_SP, SyntaxContext::empty()).into(),
                        ),
                    })),
                    right: Box::new(Expr::Lit(Lit::Num(Number {
                        span: DUMMY_SP,
                        value: 0.0,
                        raw: None,
                    }))),
                })),
                // Use null
                cons: Box::new(Expr::Lit(Lit::Null(Null { span: DUMMY_SP }))),
                // Call conversion function
                alt: Box::new(self.create_call(
                    &inner_function_name,
                    vec![self.create_arg(Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(self.create_ident(param_name)),
                        prop: MemberProp::Computed(ComputedPropName {
                            span: DUMMY_SP,
                            expr: Box::new(Expr::Lit(Lit::Num(Number {
                                span: DUMMY_SP,
                                value: 0.0,
                                raw: None,
                            }))),
                        }),
                    }))],
                )),
            }),
        }
    }
    fn convert_vec_from_candid_body(&mut self, inner: &Type, param_name: &str) -> Expr {
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
                // For numeric types, convert from TypedArray to Array using Array.from
                self.create_call(
                    "Array.from",
                    vec![self.create_arg(self.create_ident(param_name))],
                )
            }
            _ => {
                // Optimization for inner types that don't need conversion
                if !self.needs_conversion(inner) {
                    return self.create_ident(param_name);
                }

                // Get conversion function for inner type
                let inner_function_name = self.get_from_candid_function_name(inner);
                self.generate_from_candid_function(inner, &inner_function_name);

                // value.map(x => from_candid_inner(x))
                Expr::Call(CallExpr {
                    span: DUMMY_SP,
                    callee: Callee::Expr(Box::new(Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(self.create_ident(param_name)),
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
                            body: Box::new(BlockStmtOrExpr::Expr(Box::new(self.create_call(
                                &inner_function_name,
                                vec![self.create_arg(self.create_ident("x"))],
                            )))),
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

    fn convert_record_from_candid_body(&mut self, fields: &[Field], param_name: &str) -> Expr {
        // If the record is a tuple, handle differently
        if self.is_tuple(fields) {
            return self.convert_tuple_from_candid_body(fields, param_name);
        }

        // Create a new object with converted fields
        Expr::Object(ObjectLit {
            span: DUMMY_SP,
            props: fields
                .iter()
                .map(|field| {
                    let field_name = match &*field.id {
                        Label::Named(name) => name.clone(),
                        Label::Id(n) | Label::Unnamed(n) => format!("_{}_", n),
                    };

                    // Get the field from the input object
                    let field_access = Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(self.create_ident(param_name)),
                        prop: MemberProp::Ident(
                            Ident::new(field_name.clone().into(), DUMMY_SP, SyntaxContext::empty())
                                .into(),
                        ),
                    });

                    let prop_name = PropName::Ident(
                        Ident::new(field_name.into(), DUMMY_SP, SyntaxContext::empty()).into(),
                    );

                    // Convert the field value based on its type
                    let value = match field.ty.as_ref() {
                        TypeInner::Opt(_) => {
                            // For optional fields, use a utility function
                            Expr::Call(CallExpr {
                                span: DUMMY_SP,
                                callee: Callee::Expr(Box::new(Expr::Ident(Ident::new(
                                    "record_opt_to_undefined".into(),
                                    DUMMY_SP,
                                    SyntaxContext::empty(),
                                )))),
                                args: vec![ExprOrSpread {
                                    spread: None,
                                    expr: Box::new(
                                        self.convert_from_candid(&field_access, &field.ty),
                                    ),
                                }],
                                type_args: None,
                                ctxt: SyntaxContext::empty(),
                            })
                        }
                        _ => {
                            // For normal fields, check if conversion is needed
                            if !self.needs_conversion(&field.ty) {
                                field_access
                            } else {
                                // Convert the value using appropriate function
                                let function_name = self.get_from_candid_function_name(&field.ty);
                                self.generate_from_candid_function(&field.ty, &function_name);
                                self.create_call(
                                    &function_name,
                                    vec![self.create_arg(field_access)],
                                )
                            }
                        }
                    };

                    PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                        key: prop_name,
                        value: Box::new(value),
                    })))
                })
                .collect(),
        })
    }

    fn convert_tuple_from_candid_body(&mut self, fields: &[Field], param_name: &str) -> Expr {
        // Create a new array with converted fields
        Expr::Array(ArrayLit {
            span: DUMMY_SP,
            elems: fields
                .iter()
                .enumerate()
                .map(|(i, field)| {
                    // Access tuple element by index
                    let elem_access = Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(self.create_ident(param_name)),
                        prop: MemberProp::Computed(ComputedPropName {
                            span: DUMMY_SP,
                            expr: Box::new(Expr::Lit(Lit::Num(Number {
                                span: DUMMY_SP,
                                value: i as f64,
                                raw: None,
                            }))),
                        }),
                    });

                    // Check if conversion is needed
                    let value = if !self.needs_conversion(&field.ty) {
                        elem_access
                    } else {
                        // Convert the tuple element
                        let function_name = self.get_from_candid_function_name(&field.ty);
                        self.generate_from_candid_function(&field.ty, &function_name);
                        self.create_call(&function_name, vec![self.create_arg(elem_access)])
                    };

                    Some(ExprOrSpread {
                        spread: None,
                        expr: Box::new(value),
                    })
                })
                .collect(),
        })
    }

    fn convert_variant_from_candid_body(&mut self, fields: &[Field], param_name: &str) -> Expr {
        if fields.is_empty() {
            return self.create_ident(param_name);
        }
        // Check if all variants have the same type (especially null)
        let all_null = fields
            .iter()
            .all(|f| matches!(f.ty.as_ref(), TypeInner::Null));

        // For variants with all null or same simple type, return the enum member
        if all_null {
            // Determine the enum name based on whether this is a named type or anonymous
            let enum_name = self
                .enum_declarations
                .get(&fields.to_vec())
                .unwrap()
                .1
                .clone();

            let mut conditions = Vec::new();

            for field in fields {
                let field_name = match &*field.id {
                    Label::Named(name) => name.clone(),
                    Label::Id(n) | Label::Unnamed(n) => format!("_{}_", n),
                };

                // Check if this field exists in the input object
                let test = Expr::Bin(BinExpr {
                    span: DUMMY_SP,
                    op: BinaryOp::In,
                    left: Box::new(Expr::Lit(Lit::Str(Str {
                        span: DUMMY_SP,
                        value: field_name.clone().into(),
                        raw: None,
                    }))),
                    right: Box::new(self.create_ident(param_name)),
                });

                // Return the enum member access
                // let result =
                let result = if contains_unicode_characters(&field_name) {
                    Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(self.create_ident(&enum_name)),
                        prop: MemberProp::Computed(ComputedPropName {
                            span: DUMMY_SP,
                            expr: Box::new(Expr::Lit(Lit::Str(Str {
                                span: DUMMY_SP,
                                value: field_name.clone().into(),
                                raw: None,
                            }))),
                        }),
                    })
                } else {
                    Expr::Member(MemberExpr {
                        span: DUMMY_SP,
                        obj: Box::new(self.create_ident(&enum_name)),
                        prop: MemberProp::Ident(
                            Ident::new(field_name.into(), DUMMY_SP, SyntaxContext::empty()).into(),
                        ),
                    })
                };

                conditions.push((test, result));
            }

            // Build the chain of conditionals
            if conditions.is_empty() {
                // Return the input unchanged if no fields (shouldn't happen for valid variants)
                return self.create_ident(param_name);
            }

            // Start with the last condition and build in reverse
            let mut pairs = conditions.into_iter().rev();

            // Get the last pair
            let (last_test, last_result) = match pairs.next() {
                Some(pair) => pair,
                None => return self.create_ident(param_name), // Shouldn't happen due to the check above
            };

            // Build the chain
            let mut expr = Expr::Cond(CondExpr {
                span: DUMMY_SP,
                test: Box::new(last_test),
                cons: Box::new(last_result),
                // If we get here, it's an error
                alt: Box::new(self.create_ident(param_name)),
            });

            // Add the rest of the conditions
            for (test, result) in pairs {
                expr = Expr::Cond(CondExpr {
                    span: DUMMY_SP,
                    test: Box::new(test),
                    cons: Box::new(result),
                    alt: Box::new(expr),
                });
            }

            return expr;
        }

        // For variants with different types, create objects with each tag and value
        let mut conditions = Vec::new();

        for field in fields {
            let field_name = match &*field.id {
                Label::Named(name) => name.clone(),
                Label::Id(n) | Label::Unnamed(n) => format!("_{}_", n),
            };

            // Check if this field exists in the input object
            let test = Expr::Bin(BinExpr {
                span: DUMMY_SP,
                op: BinaryOp::In,
                left: Box::new(Expr::Lit(Lit::Str(Str {
                    span: DUMMY_SP,
                    value: field_name.clone().into(),
                    raw: None,
                }))),
                right: Box::new(self.create_ident(param_name)),
            });

            // Get the field value
            let field_access = Expr::Member(MemberExpr {
                span: DUMMY_SP,
                obj: Box::new(self.create_ident(param_name)),
                prop: MemberProp::Ident(
                    Ident::new(field_name.clone().into(), DUMMY_SP, SyntaxContext::empty()).into(),
                ),
            });

            // Convert the field value if needed
            let value = if !self.needs_conversion(&field.ty) {
                field_access
            } else {
                let function_name = self.get_from_candid_function_name(&field.ty);
                self.generate_from_candid_function(&field.ty, &function_name);
                self.create_call(&function_name, vec![self.create_arg(field_access)])
            };

            // Create a new object with the converted value
            let result = Expr::Object(ObjectLit {
                span: DUMMY_SP,
                props: vec![PropOrSpread::Prop(Box::new(Prop::KeyValue(KeyValueProp {
                    key: PropName::Ident(
                        Ident::new(field_name.into(), DUMMY_SP, SyntaxContext::empty()).into(),
                    ),
                    value: Box::new(value),
                })))],
            });

            conditions.push((test, result));
        }

        // Build the chain of conditionals
        if conditions.is_empty() {
            // Return the input unchanged if no fields (shouldn't happen for valid variants)
            return self.create_ident(param_name);
        }

        // Start with the last condition and build in reverse
        let mut pairs = conditions.into_iter().rev();

        // Get the last pair
        let (last_test, last_result) = match pairs.next() {
            Some(pair) => pair,
            None => return self.create_ident(param_name), // Shouldn't happen due to the check above
        };

        // Build the chain
        let mut expr = Expr::Cond(CondExpr {
            span: DUMMY_SP,
            test: Box::new(last_test),
            cons: Box::new(last_result),
            // If we get here, it's likely an error but return the input for robustness
            alt: Box::new(self.create_ident(param_name)),
        });

        // Add the rest of the conditions
        for (test, result) in pairs {
            expr = Expr::Cond(CondExpr {
                span: DUMMY_SP,
                test: Box::new(test),
                cons: Box::new(result),
                alt: Box::new(expr),
            });
        }

        expr
    }
    fn convert_func_from_candid_body(
        &mut self,
        _func: &candid::types::Function,
        param_name: &str,
    ) -> Expr {
        // Functions are represented as Principals
        self.create_ident(param_name)
    }

    // Helper to detect tuple types
    fn is_tuple(&self, fields: &[Field]) -> bool {
        if fields.is_empty() {
            return false;
        }
        for (i, field) in fields.iter().enumerate() {
            if field.id.get_id() != (i as u32) {
                return false;
            }
        }
        true
    }

    pub fn convert_to_candid(&mut self, expr: &Expr, ty: &Type) -> Expr {
        // For simple types that don't need conversion, return the expression directly
        if !self.needs_conversion(ty) {
            return expr.clone();
        }

        let function_name = self.get_to_candid_function_name(ty);

        // Generate the function if it doesn't exist
        self.generate_to_candid_function(ty, &function_name);

        // Return a call to the function
        self.create_call(&function_name, vec![self.create_arg(expr.clone())])
    }

    /// Add imports for Candid types
    pub fn add_candid_type_imports(&mut self, module: &mut Module, service_name: &str) {
        self.candid_types_converter
            .add_candid_type_imports(module, service_name);
    }

    /// Generate a function that converts from TypeScript to Candid
    fn generate_to_candid_function(&mut self, ty: &Type, function_name: &str) {
        // Skip if function already generated for this type
        if self.to_candid_generated.contains(ty) {
            return;
        }

        // Check for recursion
        let is_recursive = self.processing_to_candid.contains(ty);

        // Add to processing set to detect recursion
        self.processing_to_candid.insert(ty.clone());

        // Generate parameter type annotation
        let param_name = "value";
        let param_type_ann = self.create_ts_type_annotation(ty);

        // Generate return type annotation - use Candid type for complex types
        let return_type_ann = self.candid_types_converter.get_candid_type(ty);

        // Generate function body
        let body_expr = if is_recursive {
            // For recursive types, return a placeholder initially
            self.create_ident(param_name)
        } else {
            self.generate_to_candid_body(ty, param_name)
        };

        // Create function declaration with type annotations
        let fn_decl = Stmt::Decl(Decl::Fn(FnDecl {
            ident: Ident::new(function_name.into(), DUMMY_SP, SyntaxContext::empty()),
            declare: false,
            function: Box::new(swc_core::ecma::ast::Function {
                ctxt: SyntaxContext::empty(),
                params: vec![Param {
                    span: DUMMY_SP,
                    decorators: vec![],
                    pat: Pat::Ident(BindingIdent {
                        id: Ident::new(param_name.into(), DUMMY_SP, SyntaxContext::empty()),
                        type_ann: Some(Box::new(TsTypeAnn {
                            span: DUMMY_SP,
                            type_ann: Box::new(param_type_ann),
                        })),
                    }),
                }],
                decorators: vec![],
                span: DUMMY_SP,
                body: Some(BlockStmt {
                    span: DUMMY_SP,
                    stmts: vec![Stmt::Return(ReturnStmt {
                        span: DUMMY_SP,
                        arg: Some(Box::new(body_expr)),
                    })],
                    ctxt: SyntaxContext::empty(),
                }),
                is_generator: false,
                is_async: false,
                type_params: None,
                return_type: Some(Box::new(TsTypeAnn {
                    span: DUMMY_SP,
                    type_ann: Box::new(return_type_ann),
                })),
            }),
        }));

        self.generated_functions
            .insert(function_name.into(), fn_decl);

        // Mark this type as fully generated
        self.to_candid_generated.insert(ty.clone());

        // If recursive, update the function body now that the function exists
        if is_recursive {
            let body_expr = self.generate_to_candid_body(ty, param_name);
            if let Some(Stmt::Decl(Decl::Fn(fn_decl))) =
                self.generated_functions.get_mut(function_name)
            {
                if let Some(BlockStmt { stmts, .. }) = &mut fn_decl.function.body {
                    if let Some(Stmt::Return(ret)) = stmts.last_mut() {
                        ret.arg = Some(Box::new(body_expr));
                    }
                }
            }
        }

        // Remove from processing set
        self.processing_to_candid.remove(ty);
    }
}

pub fn convert_multi_return_from_candid(
    converter: &mut TypeConverter,
    expr: &Expr,
    types: &[Type],
) -> Expr {
    if types.is_empty() {
        // No return value, return void
        Expr::Lit(Lit::Null(Null { span: DUMMY_SP }))
    } else if types.len() == 1 {
        // Single return value
        converter.convert_from_candid(expr, &types[0])
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

                    // If type doesn't need conversion, use it directly
                    let value = if !converter.needs_conversion(ty) {
                        elem_expr
                    } else {
                        // Convert the return value using the appropriate function
                        let function_name = converter.get_from_candid_function_name(ty);
                        converter.generate_from_candid_function(ty, &function_name);
                        Expr::Call(CallExpr {
                            span: DUMMY_SP,
                            callee: Callee::Expr(Box::new(Expr::Ident(Ident::new(
                                function_name.into(),
                                DUMMY_SP,
                                SyntaxContext::empty(),
                            )))),
                            args: vec![ExprOrSpread {
                                spread: None,
                                expr: Box::new(elem_expr),
                            }],
                            type_args: None,
                            ctxt: SyntaxContext::empty(),
                        })
                    };

                    Some(ExprOrSpread {
                        spread: None,
                        expr: Box::new(value),
                    })
                })
                .collect(),
        })
    }
}
