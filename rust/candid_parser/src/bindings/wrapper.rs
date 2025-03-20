use super::javascript::is_tuple;
use candid::pretty::utils::*;
use candid::types::{Field, Function, Label, SharedLabel, Type, TypeEnv, TypeInner};
use pretty::RcDoc;

// Keep the existing constants and utility functions
// ...

//==============================================================================
// AST for TypeScript/JavaScript
//==============================================================================

#[derive(Clone, Debug)]
pub enum Expression {
    Identifier(String),
    Literal(LiteralValue),
    MemberAccess {
        object: Box<Expression>,
        property: String,
    },
    IndexAccess {
        object: Box<Expression>,
        index: Box<Expression>,
    },
    BinaryOp {
        left: Box<Expression>,
        operator: String,
        right: Box<Expression>,
    },
    TernaryOp {
        condition: Box<Expression>,
        then_expr: Box<Expression>,
        else_expr: Box<Expression>,
    },
    FunctionCall {
        function: Box<Expression>,
        arguments: Vec<Expression>,
    },
    ArrayLiteral(Vec<Expression>),
    ObjectLiteral(Vec<(String, Expression)>),
    ArrowFunction {
        params: Vec<String>,
        body: Box<Statement>,
    },
    ImmediatelyInvokedFn {
        body: Vec<Statement>,
    },
}

#[derive(Clone, Debug)]
pub enum LiteralValue {
    Null,
    Boolean(bool),
    Number(String),
    String(String),
}

#[derive(Clone, Debug)]
pub enum Statement {
    VarDeclaration {
        name: String,
        type_annotation: Option<TypeAnnotation>,
        initializer: Expression,
    },
    ExpressionStatement(Expression),
    IfStatement {
        condition: Expression,
        then_branch: Box<Statement>,
        else_branch: Option<Box<Statement>>,
    },
    ReturnStatement(Option<Expression>),
    BlockStatement(Vec<Statement>),
    ThrowStatement(Expression),
}

#[derive(Clone, Debug)]
pub enum TypeAnnotation {
    NamedType(String),
    ArrayType(Box<TypeAnnotation>),
    ObjectType(Vec<(String, TypeAnnotation)>),
    TupleType(Vec<TypeAnnotation>),
    UnionType(Vec<TypeAnnotation>),
    NullableType(Box<TypeAnnotation>),
    FunctionType {
        params: Vec<(String, TypeAnnotation)>,
        return_type: Box<TypeAnnotation>,
    },
}

//==============================================================================
// AST Renderer - Converts AST to RcDoc
//==============================================================================

pub struct AstRenderer<'a> {
    env: &'a TypeEnv,
}

impl<'a> AstRenderer<'a> {
    pub fn new(env: &'a TypeEnv) -> Self {
        AstRenderer { env }
    }

    pub fn render_expression(&self, expr: &Expression) -> RcDoc<'a> {
        match expr {
            Expression::Identifier(name) => str(name),
            Expression::Literal(value) => self.render_literal(value),
            Expression::MemberAccess { object, property } => self
                .render_expression(object)
                .append(str("."))
                .append(str(property)),
            Expression::IndexAccess { object, index } => self
                .render_expression(object)
                .append(str("["))
                .append(self.render_expression(index))
                .append(str("]")),
            Expression::BinaryOp {
                left,
                operator,
                right,
            } => self
                .render_expression(left)
                .append(str(" "))
                .append(str(operator))
                .append(str(" "))
                .append(self.render_expression(right)),
            Expression::TernaryOp {
                condition,
                then_expr,
                else_expr,
            } => self
                .render_expression(condition)
                .append(str(" ? "))
                .append(self.render_expression(then_expr))
                .append(str(" : "))
                .append(self.render_expression(else_expr)),
            Expression::FunctionCall {
                function,
                arguments,
            } => {
                let args = RcDoc::intersperse(
                    arguments.iter().map(|arg| self.render_expression(arg)),
                    str(", "),
                );

                self.render_expression(function)
                    .append(str("("))
                    .append(args)
                    .append(str(")"))
            }
            Expression::ArrayLiteral(elements) => {
                let elems = RcDoc::intersperse(
                    elements.iter().map(|elem| self.render_expression(elem)),
                    str(", "),
                );

                str("[").append(elems).append(str("]"))
            }
            Expression::ObjectLiteral(properties) => {
                let props = properties.iter().map(|(key, value)| {
                    str(key)
                        .append(str(": "))
                        .append(self.render_expression(value))
                });

                let props_doc = RcDoc::intersperse(props, str(", "));

                str("{ ").append(props_doc).append(str(" }"))
            }
            Expression::ArrowFunction { params, body } => {
                let params_doc =
                    RcDoc::intersperse(params.iter().map(|param| str(param)), str(", "));

                str("(")
                    .append(params_doc)
                    .append(str(") => "))
                    .append(self.render_statement(body))
            }
            Expression::ImmediatelyInvokedFn { body } => {
                let body_doc = RcDoc::intersperse(
                    body.iter()
                        .map(|stmt| self.render_statement(stmt).append(RcDoc::line())),
                    RcDoc::nil(),
                );

                str("(() => {")
                    .append(RcDoc::line())
                    .append(body_doc)
                    .append(str("})()"))
            }
        }
    }

    fn render_literal(&self, lit: &LiteralValue) -> RcDoc<'a> {
        match lit {
            LiteralValue::Null => str("null"),
            LiteralValue::Boolean(value) => str(if *value { "true" } else { "false" }),
            LiteralValue::Number(value) => str(value),
            LiteralValue::String(value) => str("\"").append(str(value)).append(str("\"")),
        }
    }

    pub fn render_statement(&self, stmt: &Statement) -> RcDoc<'a> {
        match stmt {
            Statement::VarDeclaration {
                name,
                type_annotation,
                initializer,
            } => {
                let mut doc = str("const ").append(str(name));

                if let Some(type_ann) = type_annotation {
                    doc = doc
                        .append(str(": "))
                        .append(self.render_type_annotation(type_ann));
                }

                doc.append(str(" = "))
                    .append(self.render_expression(initializer))
                    .append(str(";"))
            }
            Statement::ExpressionStatement(expr) => self.render_expression(expr).append(str(";")),
            Statement::IfStatement {
                condition,
                then_branch,
                else_branch,
            } => {
                let mut doc = str("if (")
                    .append(self.render_expression(condition))
                    .append(str(") "))
                    .append(self.render_statement(then_branch));

                if let Some(else_stmt) = else_branch {
                    doc = doc
                        .append(str(" else "))
                        .append(self.render_statement(else_stmt));
                }

                doc
            }
            Statement::ReturnStatement(expr) => {
                let mut doc = str("return");

                if let Some(e) = expr {
                    doc = doc.append(str(" ")).append(self.render_expression(e));
                }

                doc.append(str(";"))
            }
            Statement::BlockStatement(stmts) => {
                let stmts_doc = RcDoc::intersperse(
                    stmts
                        .iter()
                        .map(|s| self.render_statement(s).append(RcDoc::line())),
                    RcDoc::nil(),
                );

                str("{")
                    .append(RcDoc::line())
                    .append(stmts_doc)
                    .append(str("}"))
            }
            Statement::ThrowStatement(expr) => str("throw ")
                .append(self.render_expression(expr))
                .append(str(";")),
        }
    }

    pub fn render_type_annotation(&self, type_ann: &TypeAnnotation) -> RcDoc<'a> {
        match type_ann {
            TypeAnnotation::NamedType(name) => str(name),
            TypeAnnotation::ArrayType(element_type) => str("Array<")
                .append(self.render_type_annotation(element_type))
                .append(str(">")),
            TypeAnnotation::ObjectType(properties) => {
                let props = properties.iter().map(|(key, value)| {
                    str(key)
                        .append(str(": "))
                        .append(self.render_type_annotation(value))
                });

                let props_doc = RcDoc::intersperse(props, str(", "));

                str("{ ").append(props_doc).append(str(" }"))
            }
            TypeAnnotation::TupleType(elements) => {
                let elems = RcDoc::intersperse(
                    elements
                        .iter()
                        .map(|elem| self.render_type_annotation(elem)),
                    str(", "),
                );

                str("[").append(elems).append(str("]"))
            }
            TypeAnnotation::UnionType(types) => {
                let types_doc = RcDoc::intersperse(
                    types.iter().map(|t| self.render_type_annotation(t)),
                    str(" | "),
                );

                types_doc
            }
            TypeAnnotation::NullableType(inner) => {
                self.render_type_annotation(inner).append(str(" | null"))
            }
            TypeAnnotation::FunctionType {
                params,
                return_type,
            } => {
                let params_doc = RcDoc::intersperse(
                    params.iter().map(|(name, t)| {
                        str(name)
                            .append(str(": "))
                            .append(self.render_type_annotation(t))
                    }),
                    str(", "),
                );

                str("(")
                    .append(params_doc)
                    .append(str(") => "))
                    .append(self.render_type_annotation(return_type))
            }
        }
    }
}

//==============================================================================
// Type Converter Infrastructure
//==============================================================================

#[derive(Clone, Copy, Debug)]
pub enum ConversionDirection {
    ToCandid,
    ToTypeScript,
}

pub struct Converter<'a> {
    env: &'a TypeEnv,
    direction: ConversionDirection,
}

impl<'a> Converter<'a> {
    pub fn new(env: &'a TypeEnv, direction: ConversionDirection) -> Self {
        Converter { env, direction }
    }

    pub fn convert(&self, ty: &'a Type, input: &str, output: &str) -> Statement {
        let input_expr = Expression::Identifier(input.to_string());
        self.convert_type(ty, input_expr, output)
    }

    fn convert_type(&self, ty: &'a Type, input_expr: Expression, output_var: &str) -> Statement {
        match ty.as_ref() {
            TypeInner::Null => self.convert_null(input_expr, output_var),
            TypeInner::Bool => self.convert_primitive(ty, input_expr, output_var),
            TypeInner::Nat
            | TypeInner::Int
            | TypeInner::Nat8
            | TypeInner::Nat16
            | TypeInner::Nat32
            | TypeInner::Nat64
            | TypeInner::Int8
            | TypeInner::Int16
            | TypeInner::Int32
            | TypeInner::Int64
            | TypeInner::Float32
            | TypeInner::Float64
            | TypeInner::Text
            | TypeInner::Reserved
            | TypeInner::Empty
            | TypeInner::Principal => self.convert_primitive(ty, input_expr, output_var),
            TypeInner::Opt(inner) => self.convert_optional(ty, inner, input_expr, output_var),
            TypeInner::Vec(inner) => self.convert_vector(ty, inner, input_expr, output_var),
            TypeInner::Record(fields) => {
                if is_tuple(ty) {
                    self.convert_tuple(ty, fields, input_expr, output_var)
                } else {
                    self.convert_record(ty, fields, input_expr, output_var)
                }
            }
            TypeInner::Variant(fields) => self.convert_variant(ty, fields, input_expr, output_var),
            TypeInner::Var(id) => self.convert_type_var(ty, id, input_expr, output_var),
            _ => self.convert_primitive(ty, input_expr, output_var), // Fallback
        }
    }

    // Conversion implementations for each type

    fn convert_null(&self, input_expr: Expression, output_var: &str) -> Statement {
        match self.direction {
            ConversionDirection::ToCandid => {
                // TypeScript null to Candid null - simple passthrough
                Statement::VarDeclaration {
                    name: output_var.to_string(),
                    type_annotation: None,
                    initializer: input_expr,
                }
            }
            ConversionDirection::ToTypeScript => {
                // Candid null to TypeScript null
                Statement::VarDeclaration {
                    name: output_var.to_string(),
                    type_annotation: Some(TypeAnnotation::NamedType("null".to_string())),
                    initializer: input_expr,
                }
            }
        }
    }

    fn convert_primitive(
        &self,
        ty: &'a Type,
        input_expr: Expression,
        output_var: &str,
    ) -> Statement {
        match self.direction {
            ConversionDirection::ToCandid => {
                // TypeScript primitive to Candid - simple passthrough
                Statement::VarDeclaration {
                    name: output_var.to_string(),
                    type_annotation: None,
                    initializer: input_expr,
                }
            }
            ConversionDirection::ToTypeScript => {
                // Candid primitive to TypeScript with type annotation
                let type_annotation = self.type_to_annotation(ty);
                Statement::VarDeclaration {
                    name: output_var.to_string(),
                    type_annotation: Some(type_annotation),
                    initializer: input_expr,
                }
            }
        }
    }

    fn convert_optional(
        &self,
        ty: &'a Type,
        inner: &'a Type,
        input_expr: Expression,
        output_var: &str,
    ) -> Statement {
        match self.direction {
            ConversionDirection::ToCandid => {
                // TypeScript null|T to Candid opt
                if self.needs_conversion(inner) {
                    // Complex case with inner conversions
                    let inner_tmp = format!("{}_inner", output_var);
                    let inner_expr = Expression::Identifier(inner_tmp.clone());
                    let inner_stmt = self.convert_type(inner, inner_expr, &inner_tmp);

                    // Create an IIFE for the conversion
                    let body = vec![
                        Statement::IfStatement {
                            condition: Expression::BinaryOp {
                                left: Box::new(input_expr.clone()),
                                operator: "===".to_string(),
                                right: Box::new(Expression::Literal(LiteralValue::Null)),
                            },
                            then_branch: Box::new(Statement::ReturnStatement(Some(
                                Expression::ArrayLiteral(vec![]),
                            ))),
                            else_branch: None,
                        },
                        Statement::VarDeclaration {
                            name: inner_tmp.clone(),
                            type_annotation: None,
                            initializer: input_expr.clone(),
                        },
                        inner_stmt,
                        Statement::ReturnStatement(Some(Expression::ArrayLiteral(vec![
                            Expression::Identifier(inner_tmp),
                        ]))),
                    ];

                    Statement::VarDeclaration {
                        name: output_var.to_string(),
                        type_annotation: None,
                        initializer: Expression::ImmediatelyInvokedFn { body },
                    }
                } else {
                    // Simple case without nested conversions
                    Statement::VarDeclaration {
                        name: output_var.to_string(),
                        type_annotation: None,
                        initializer: Expression::TernaryOp {
                            condition: Box::new(Expression::BinaryOp {
                                left: Box::new(input_expr.clone()),
                                operator: "===".to_string(),
                                right: Box::new(Expression::Literal(LiteralValue::Null)),
                            }),
                            then_expr: Box::new(Expression::ArrayLiteral(vec![])),
                            else_expr: Box::new(Expression::ArrayLiteral(vec![input_expr])),
                        },
                    }
                }
            }
            ConversionDirection::ToTypeScript => {
                // Candid opt to TypeScript null|T
                let type_annotation =
                    TypeAnnotation::NullableType(Box::new(self.type_to_annotation(inner)));

                if self.needs_conversion(inner) {
                    // Complex case with inner conversions
                    let inner_tmp = format!("{}_inner", output_var);
                    let inner_expr = Expression::Identifier(inner_tmp.clone());
                    let inner_stmt = self.convert_type(inner, inner_expr, &inner_tmp);

                    // Create an IIFE for the conversion
                    let body = vec![
                        Statement::IfStatement {
                            condition: Expression::BinaryOp {
                                left: Box::new(Expression::MemberAccess {
                                    object: Box::new(input_expr.clone()),
                                    property: "length".to_string(),
                                }),
                                operator: "===".to_string(),
                                right: Box::new(Expression::Literal(LiteralValue::Number(
                                    "0".to_string(),
                                ))),
                            },
                            then_branch: Box::new(Statement::ReturnStatement(Some(
                                Expression::Literal(LiteralValue::Null),
                            ))),
                            else_branch: None,
                        },
                        Statement::VarDeclaration {
                            name: inner_tmp.clone(),
                            type_annotation: None,
                            initializer: Expression::IndexAccess {
                                object: Box::new(input_expr),
                                index: Box::new(Expression::Literal(LiteralValue::Number(
                                    "0".to_string(),
                                ))),
                            },
                        },
                        inner_stmt,
                        Statement::ReturnStatement(Some(Expression::Identifier(inner_tmp))),
                    ];

                    Statement::VarDeclaration {
                        name: output_var.to_string(),
                        type_annotation: Some(type_annotation),
                        initializer: Expression::ImmediatelyInvokedFn { body },
                    }
                } else {
                    // Simple case without nested conversions
                    Statement::VarDeclaration {
                        name: output_var.to_string(),
                        type_annotation: Some(type_annotation),
                        initializer: Expression::TernaryOp {
                            condition: Expression::BinaryOp {
                                left: Box::new(Expression::MemberAccess {
                                    object: Box::new(input_expr.clone()),
                                    property: "length".to_string(),
                                }),
                                operator: "===".to_string(),
                                right: Box::new(Expression::Literal(LiteralValue::Number(
                                    "0".to_string(),
                                ))),
                            },
                            then_expr: Box::new(Expression::Literal(LiteralValue::Null)),
                            else_expr: Box::new(Expression::IndexAccess {
                                object: Box::new(input_expr),
                                index: Box::new(Expression::Literal(LiteralValue::Number(
                                    "0".to_string(),
                                ))),
                            }),
                        },
                    }
                }
            }
        }
    }

    fn convert_vector(
        &self,
        ty: &'a Type,
        inner: &'a Type,
        input_expr: Expression,
        output_var: &str,
    ) -> Statement {
        // Implementation for vector conversion
        if self.needs_conversion(inner) {
            // If the array elements need conversion, we need to map over them
            let el_param = "el".to_string();
            let el_expr = Expression::Identifier(el_param.clone());

            // Create inner conversion
            let result_param = "result".to_string();
            let inner_stmt = self.convert_type(inner, el_expr.clone(), &result_param);

            // Create map function body
            let map_body = match inner_stmt {
                Statement::VarDeclaration { initializer, .. } => Expression::ArrowFunction {
                    params: vec![el_param],
                    body: Box::new(Statement::ReturnStatement(Some(initializer))),
                },
                _ => {
                    // Fallback for complex statements - wrap in block
                    Expression::ArrowFunction {
                        params: vec![el_param],
                        body: Box::new(Statement::BlockStatement(vec![
                            inner_stmt,
                            Statement::ReturnStatement(Some(Expression::Identifier(result_param))),
                        ])),
                    }
                }
            };

            // Create map expression
            let map_expr = Expression::FunctionCall {
                function: Box::new(Expression::MemberAccess {
                    object: Box::new(input_expr),
                    property: "map".to_string(),
                }),
                arguments: vec![map_body],
            };

            // Output with type annotation if needed
            match self.direction {
                ConversionDirection::ToCandid => Statement::VarDeclaration {
                    name: output_var.to_string(),
                    type_annotation: None,
                    initializer: map_expr,
                },
                ConversionDirection::ToTypeScript => Statement::VarDeclaration {
                    name: output_var.to_string(),
                    type_annotation: Some(self.type_to_annotation(ty)),
                    initializer: map_expr,
                },
            }
        } else {
            // Special handling for typed arrays if needed
            match self.direction {
                ConversionDirection::ToCandid => {
                    // Check if the inner type is a numeric type that might need special handling
                    match inner.as_ref() {
                        TypeInner::Nat8
                        | TypeInner::Nat16
                        | TypeInner::Nat32
                        | TypeInner::Int8
                        | TypeInner::Int16
                        | TypeInner::Int32 => {
                            // Handle numeric typed arrays
                            let array_type = match inner.as_ref() {
                                TypeInner::Nat8 => "Uint8Array",
                                TypeInner::Nat16 => "Uint16Array",
                                TypeInner::Nat32 => "Uint32Array",
                                TypeInner::Int8 => "Int8Array",
                                TypeInner::Int16 => "Int16Array",
                                TypeInner::Int32 => "Int32Array",
                                _ => unreachable!(),
                            };

                            let conversion = Expression::TernaryOp {
                                condition: Box::new(Expression::FunctionCall {
                                    function: Box::new(Expression::MemberAccess {
                                        object: Box::new(Expression::Identifier(
                                            "Array".to_string(),
                                        )),
                                        property: "isArray".to_string(),
                                    }),
                                    arguments: vec![input_expr.clone()],
                                }),
                                then_expr: Box::new(Expression::FunctionCall {
                                    function: Box::new(Expression::Identifier(format!(
                                        "new {}",
                                        array_type
                                    ))),
                                    arguments: vec![input_expr.clone()],
                                }),
                                else_expr: Box::new(input_expr),
                            };

                            Statement::VarDeclaration {
                                name: output_var.to_string(),
                                type_annotation: None,
                                initializer: conversion,
                            }
                        }
                        TypeInner::Nat64 | TypeInner::Int64 => {
                            // Handle BigInt arrays
                            let array_type = match inner.as_ref() {
                                TypeInner::Nat64 => "BigUint64Array",
                                TypeInner::Int64 => "BigInt64Array",
                                _ => unreachable!(),
                            };

                            let conversion = Expression::TernaryOp {
                                condition: Box::new(Expression::FunctionCall {
                                    function: Box::new(Expression::MemberAccess {
                                        object: Box::new(Expression::Identifier(
                                            "Array".to_string(),
                                        )),
                                        property: "isArray".to_string(),
                                    }),
                                    arguments: vec![input_expr.clone()],
                                }),
                                then_expr: Box::new(Expression::FunctionCall {
                                    function: Box::new(Expression::Identifier(format!(
                                        "new {}",
                                        array_type
                                    ))),
                                    arguments: vec![Expression::FunctionCall {
                                        function: Box::new(Expression::MemberAccess {
                                            object: Box::new(input_expr.clone()),
                                            property: "map".to_string(),
                                        }),
                                        arguments: vec![Expression::ArrowFunction {
                                            params: vec!["n".to_string()],
                                            body: Box::new(Statement::ReturnStatement(Some(
                                                Expression::FunctionCall {
                                                    function: Box::new(Expression::Identifier(
                                                        "BigInt".to_string(),
                                                    )),
                                                    arguments: vec![Expression::Identifier(
                                                        "n".to_string(),
                                                    )],
                                                },
                                            ))),
                                        }],
                                    }],
                                }),
                                else_expr: Box::new(input_expr),
                            };

                            Statement::VarDeclaration {
                                name: output_var.to_string(),
                                type_annotation: None,
                                initializer: conversion,
                            }
                        }
                        _ => {
                            // Simple passthrough for other types
                            Statement::VarDeclaration {
                                name: output_var.to_string(),
                                type_annotation: None,
                                initializer: input_expr,
                            }
                        }
                    }
                }
                ConversionDirection::ToTypeScript => {
                    // Simple passthrough with type annotation
                    Statement::VarDeclaration {
                        name: output_var.to_string(),
                        type_annotation: Some(self.type_to_annotation(ty)),
                        initializer: input_expr,
                    }
                }
            }
        }
    }

    fn convert_record(
        &self,
        ty: &'a Type,
        fields: &'a [Field],
        input_expr: Expression,
        output_var: &str,
    ) -> Statement {
        if fields.iter().any(|f| self.needs_conversion(&f.ty)) {
            // Complex case: some fields need conversion
            let field_conversions = fields
                .iter()
                .map(|f| {
                    let field_name = match &*f.id {
                        Label::Named(name) => name.clone(),
                        Label::Id(n) | Label::Unnamed(n) => format!("_{}_", n),
                    };

                    let field_expr = Expression::MemberAccess {
                        object: Box::new(input_expr.clone()),
                        property: field_name.clone(),
                    };

                    let field_var = format!("{}_field_{}", output_var, field_name);
                    let field_stmt = self.convert_type(&f.ty, field_expr, &field_var);

                    match field_stmt {
                        Statement::VarDeclaration { initializer, .. } => (field_name, initializer),
                        _ => {
                            // This is a complex statement that we'll have to handle specially
                            // For now, we'll just use the field as-is
                            (
                                field_name,
                                Expression::MemberAccess {
                                    object: Box::new(input_expr.clone()),
                                    property: field_name.clone(),
                                },
                            )
                        }
                    }
                })
                .collect::<Vec<_>>();

            // Create object literal with converted fields
            let object_expr = Expression::ObjectLiteral(field_conversions);

            match self.direction {
                ConversionDirection::ToCandid => Statement::VarDeclaration {
                    name: output_var.to_string(),
                    type_annotation: None,
                    initializer: object_expr,
                },
                ConversionDirection::ToTypeScript => Statement::VarDeclaration {
                    name: output_var.to_string(),
                    type_annotation: Some(self.type_to_annotation(ty)),
                    initializer: object_expr,
                },
            }
        } else {
            // Simple case: no fields need conversion
            match self.direction {
                ConversionDirection::ToCandid => Statement::VarDeclaration {
                    name: output_var.to_string(),
                    type_annotation: None,
                    initializer: input_expr,
                },
                ConversionDirection::ToTypeScript => Statement::VarDeclaration {
                    name: output_var.to_string(),
                    type_annotation: Some(self.type_to_annotation(ty)),
                    initializer: input_expr,
                },
            }
        }
    }

    fn convert_tuple(
        &self,
        ty: &'a Type,
        fields: &'a [Field],
        input_expr: Expression,
        output_var: &str,
    ) -> Statement {
        if fields.iter().any(|f| self.needs_conversion(&f.ty)) {
            // Complex case: some elements need conversion
            let element_conversions = fields
                .iter()
                .enumerate()
                .map(|(i, f)| {
                    let elem_expr = Expression::IndexAccess {
                        object: Box::new(input_expr.clone()),
                        index: Box::new(Expression::Literal(LiteralValue::Number(i.to_string()))),
                    };

                    let elem_var = format!("{}_elem{}", output_var, i);
                    let elem_stmt = self.convert_type(&f.ty, elem_expr, &elem_var);

                    match elem_stmt {
                        Statement::VarDeclaration { initializer, .. } => initializer,
                        _ => {
                            // For complex statements, use the element as-is
                            Expression::IndexAccess {
                                object: Box::new(input_expr.clone()),
                                index: Box::new(Expression::Literal(LiteralValue::Number(
                                    i.to_string(),
                                ))),
                            }
                        }
                    }
                })
                .collect::<Vec<_>>();

            // Create array literal with converted elements
            let array_expr = Expression::ArrayLiteral(element_conversions);

            match self.direction {
                ConversionDirection::ToCandid => Statement::VarDeclaration {
                    name: output_var.to_string(),
                    type_annotation: None,
                    initializer: array_expr,
                },
                ConversionDirection::ToTypeScript => Statement::VarDeclaration {
                    name: output_var.to_string(),
                    type_annotation: Some(self.type_to_annotation(ty)),
                    initializer: array_expr,
                },
            }
        } else {
            // Simple case: no elements need conversion
            match self.direction {
                ConversionDirection::ToCandid => Statement::VarDeclaration {
                    name: output_var.to_string(),
                    type_annotation: None,
                    initializer: input_expr,
                },
                ConversionDirection::ToTypeScript => Statement::VarDeclaration {
                    name: output_var.to_string(),
                    type_annotation: Some(self.type_to_annotation(ty)),
                    initializer: input_expr,
                },
            }
        }
    }

    fn convert_variant(
        &self,
        ty: &'a Type,
        fields: &'a [Field],
        input_expr: Expression,
        output_var: &str,
    ) -> Statement {
        if fields.iter().any(|f| self.needs_conversion(&f.ty)) {
            // Complex case: variant fields need conversions
            let variant_cases = fields
                .iter()
                .map(|f| {
                    let field_name = match &*f.id {
                        Label::Named(name) => name.clone(),
                        Label::Id(n) | Label::Unnamed(n) => format!("_{}_", n),
                    };

                    let field_expr = Expression::MemberAccess {
                        object: Box::new(input_expr.clone()),
                        property: field_name.clone(),
                    };

                    let field_var = format!("{}_variant_{}", output_var, field_name);
                    let field_stmt = self.convert_type(&f.ty, field_expr, &field_var);

                    // Create if statement for this variant case
                    let condition = Expression::BinaryOp {
                        left: Box::new(Expression::Literal(LiteralValue::String(
                            field_name.clone(),
                        ))),
                        operator: "in".to_string(),
                        right: Box::new(input_expr.clone()),
                    };

                    // Return expression creates the variant object for this case
                    let return_expr = match field_stmt {
                        Statement::VarDeclaration { initializer, .. } => {
                            Expression::ObjectLiteral(vec![(field_name, initializer)])
                        }
                        _ => {
                            // For complex field statements, use a placeholder
                            Expression::ObjectLiteral(vec![(
                                field_name.clone(),
                                Expression::MemberAccess {
                                    object: Box::new(input_expr.clone()),
                                    property: field_name,
                                },
                            )])
                        }
                    };

                    Statement::IfStatement {
                        condition,
                        then_branch: Box::new(Statement::ReturnStatement(Some(return_expr))),
                        else_branch: None,
                    }
                })
                .collect::<Vec<_>>();

            // Add error case at the end
            let error_stmt = Statement::ThrowStatement(Expression::FunctionCall {
                function: Box::new(Expression::Identifier("Error".to_string())),
                arguments: vec![Expression::Literal(LiteralValue::String(format!(
                    "Unknown variant in {}",
                    output_var
                )))],
            });

            let mut variant_body = variant_cases;
            variant_body.push(error_stmt);

            let variant_expr = Expression::ImmediatelyInvokedFn { body: variant_body };

            match self.direction {
                ConversionDirection::ToCandid => Statement::VarDeclaration {
                    name: output_var.to_string(),
                    type_annotation: None,
                    initializer: variant_expr,
                },
                ConversionDirection::ToTypeScript => Statement::VarDeclaration {
                    name: output_var.to_string(),
                    type_annotation: Some(self.type_to_annotation(ty)),
                    initializer: variant_expr,
                },
            }
        } else {
            // Simple case: no conversions needed
            match self.direction {
                ConversionDirection::ToCandid => Statement::VarDeclaration {
                    name: output_var.to_string(),
                    type_annotation: None,
                    initializer: input_expr,
                },
                ConversionDirection::ToTypeScript => Statement::VarDeclaration {
                    name: output_var.to_string(),
                    type_annotation: Some(self.type_to_annotation(ty)),
                    initializer: input_expr,
                },
            }
        }
    }

    fn convert_type_var(
        &self,
        ty: &'a Type,
        id: &'a str,
        input_expr: Expression,
        output_var: &str,
    ) -> Statement {
        if let Ok(resolved_ty) = self.env.rec_find_type(id) {
            if self.needs_conversion(resolved_ty) {
                // If the resolved type needs conversion, delegate to it
                self.convert_type(resolved_ty, input_expr, output_var)
            } else {
                // Simple passthrough if no conversion needed
                match self.direction {
                    ConversionDirection::ToCandid => Statement::VarDeclaration {
                        name: output_var.to_string(),
                        type_annotation: None,
                        initializer: input_expr,
                    },
                    ConversionDirection::ToTypeScript => Statement::VarDeclaration {
                        name: output_var.to_string(),
                        type_annotation: Some(self.type_to_annotation(ty)),
                        initializer: input_expr,
                    },
                }
            }
        } else {
            // Can't resolve, just pass through with any type
            match self.direction {
                ConversionDirection::ToCandid => Statement::VarDeclaration {
                    name: output_var.to_string(),
                    type_annotation: None,
                    initializer: input_expr,
                },
                ConversionDirection::ToTypeScript => Statement::VarDeclaration {
                    name: output_var.to_string(),
                    type_annotation: Some(TypeAnnotation::NamedType("any".to_string())),
                    initializer: input_expr,
                },
            }
        }
    }

    // Helper method to convert Candid type to TypeScript type annotation
    fn type_to_annotation(&self, ty: &'a Type) -> TypeAnnotation {
        match ty.as_ref() {
            TypeInner::Null => TypeAnnotation::NamedType("null".to_string()),
            TypeInner::Bool => TypeAnnotation::NamedType("boolean".to_string()),
            TypeInner::Nat => TypeAnnotation::NamedType("bigint".to_string()),
            TypeInner::Int => TypeAnnotation::NamedType("bigint".to_string()),
            TypeInner::Nat8 => TypeAnnotation::NamedType("number".to_string()),
            TypeInner::Nat16 => TypeAnnotation::NamedType("number".to_string()),
            TypeInner::Nat32 => TypeAnnotation::NamedType("number".to_string()),
            TypeInner::Nat64 => TypeAnnotation::NamedType("bigint".to_string()),
            TypeInner::Int8 => TypeAnnotation::NamedType("number".to_string()),
            TypeInner::Int16 => TypeAnnotation::NamedType("number".to_string()),
            TypeInner::Int32 => TypeAnnotation::NamedType("number".to_string()),
            TypeInner::Int64 => TypeAnnotation::NamedType("bigint".to_string()),
            TypeInner::Float32 => TypeAnnotation::NamedType("number".to_string()),
            TypeInner::Float64 => TypeAnnotation::NamedType("number".to_string()),
            TypeInner::Text => TypeAnnotation::NamedType("string".to_string()),
            TypeInner::Reserved => TypeAnnotation::NamedType("any".to_string()),
            TypeInner::Empty => TypeAnnotation::NamedType("never".to_string()),
            TypeInner::Principal => TypeAnnotation::NamedType("Principal".to_string()),
            TypeInner::Opt(inner) => {
                TypeAnnotation::NullableType(Box::new(self.type_to_annotation(inner)))
            }
            TypeInner::Vec(inner) => {
                // Special handling for numeric types
                match inner.as_ref() {
                    TypeInner::Nat8 => TypeAnnotation::UnionType(vec![
                        TypeAnnotation::NamedType("Uint8Array".to_string()),
                        TypeAnnotation::ArrayType(Box::new(TypeAnnotation::NamedType(
                            "number".to_string(),
                        ))),
                    ]),
                    TypeInner::Nat16 => TypeAnnotation::UnionType(vec![
                        TypeAnnotation::NamedType("Uint16Array".to_string()),
                        TypeAnnotation::ArrayType(Box::new(TypeAnnotation::NamedType(
                            "number".to_string(),
                        ))),
                    ]),
                    TypeInner::Nat32 => TypeAnnotation::UnionType(vec![
                        TypeAnnotation::NamedType("Uint32Array".to_string()),
                        TypeAnnotation::ArrayType(Box::new(TypeAnnotation::NamedType(
                            "number".to_string(),
                        ))),
                    ]),
                    TypeInner::Nat64 => TypeAnnotation::UnionType(vec![
                        TypeAnnotation::NamedType("BigUint64Array".to_string()),
                        TypeAnnotation::ArrayType(Box::new(TypeAnnotation::NamedType(
                            "bigint".to_string(),
                        ))),
                    ]),
                    TypeInner::Int8 => TypeAnnotation::UnionType(vec![
                        TypeAnnotation::NamedType("Int8Array".to_string()),
                        TypeAnnotation::ArrayType(Box::new(TypeAnnotation::NamedType(
                            "number".to_string(),
                        ))),
                    ]),
                    TypeInner::Int16 => TypeAnnotation::UnionType(vec![
                        TypeAnnotation::NamedType("Int16Array".to_string()),
                        TypeAnnotation::ArrayType(Box::new(TypeAnnotation::NamedType(
                            "number".to_string(),
                        ))),
                    ]),
                    TypeInner::Int32 => TypeAnnotation::UnionType(vec![
                        TypeAnnotation::NamedType("Int32Array".to_string()),
                        TypeAnnotation::ArrayType(Box::new(TypeAnnotation::NamedType(
                            "number".to_string(),
                        ))),
                    ]),
                    TypeInner::Int64 => TypeAnnotation::UnionType(vec![
                        TypeAnnotation::NamedType("BigInt64Array".to_string()),
                        TypeAnnotation::ArrayType(Box::new(TypeAnnotation::NamedType(
                            "bigint".to_string(),
                        ))),
                    ]),
                    _ => TypeAnnotation::ArrayType(Box::new(self.type_to_annotation(inner))),
                }
            }
            TypeInner::Record(fields) => {
                if is_tuple(ty) {
                    // Tuple type
                    let element_types = fields
                        .iter()
                        .map(|f| self.type_to_annotation(&f.ty))
                        .collect();

                    TypeAnnotation::TupleType(element_types)
                } else {
                    // Record type
                    let properties = fields
                        .iter()
                        .map(|f| {
                            let field_name = match &*f.id {
                                Label::Named(name) => name.clone(),
                                Label::Id(n) | Label::Unnamed(n) => format!("_{}_", n),
                            };

                            // Handle optional fields with question mark syntax
                            match f.ty.as_ref() {
                                TypeInner::Opt(inner) => {
                                    (format!("{}?", field_name), self.type_to_annotation(inner))
                                }
                                _ => (field_name, self.type_to_annotation(&f.ty)),
                            }
                        })
                        .collect();

                    TypeAnnotation::ObjectType(properties)
                }
            }
            TypeInner::Variant(fields) => {
                if fields.is_empty() {
                    TypeAnnotation::NamedType("never".to_string())
                } else {
                    // Union of variant objects
                    let variant_types = fields
                        .iter()
                        .map(|f| {
                            let field_name = match &*f.id {
                                Label::Named(name) => name.clone(),
                                Label::Id(n) | Label::Unnamed(n) => format!("_{}_", n),
                            };

                            TypeAnnotation::ObjectType(vec![(
                                field_name,
                                self.type_to_annotation(&f.ty),
                            )])
                        })
                        .collect();

                    TypeAnnotation::UnionType(variant_types)
                }
            }
            TypeInner::Var(id) => {
                if let Ok(resolved) = self.env.rec_find_type(id) {
                    // If we can resolve it, use the resolved type
                    if matches!(
                        resolved.as_ref(),
                        TypeInner::Service(_) | TypeInner::Func(_)
                    ) {
                        self.type_to_annotation(resolved)
                    } else {
                        TypeAnnotation::NamedType(id.clone())
                    }
                } else {
                    // Otherwise just use the name
                    TypeAnnotation::NamedType(id.clone())
                }
            }
            TypeInner::Func(func) => {
                let params = func
                    .args
                    .iter()
                    .enumerate()
                    .map(|(i, ty)| (format!("arg{}", i), self.type_to_annotation(ty)))
                    .collect();

                let return_type = match func.rets.len() {
                    0 => Box::new(TypeAnnotation::NamedType("void".to_string())),
                    1 => Box::new(self.type_to_annotation(&func.rets[0])),
                    _ => {
                        let ret_types = func
                            .rets
                            .iter()
                            .map(|ty| self.type_to_annotation(ty))
                            .collect();

                        Box::new(TypeAnnotation::TupleType(ret_types))
                    }
                };

                TypeAnnotation::FunctionType {
                    params,
                    return_type,
                }
            }
            TypeInner::Service(_) => TypeAnnotation::NamedType("Principal".to_string()),
            _ => TypeAnnotation::NamedType("any".to_string()), // Fallback for unknown types
        }
    }

    // Helper method to check if a type needs special conversion
    fn needs_conversion(&self, ty: &'a Type) -> bool {
        match ty.as_ref() {
            TypeInner::Opt(_) => true,
            TypeInner::Vec(inner) => self.needs_conversion(inner),
            TypeInner::Record(fields) => fields.iter().any(|f| self.needs_conversion(&f.ty)),
            TypeInner::Variant(fields) => fields.iter().any(|f| self.needs_conversion(&f.ty)),
            TypeInner::Var(id) => {
                if let Ok(resolved) = self.env.rec_find_type(id) {
                    self.needs_conversion(resolved)
                } else {
                    false
                }
            }
            _ => false,
        }
    }
}

//==============================================================================
// Public Interface Functions
//==============================================================================

// Main entry point for type conversion
pub fn convert_between_types<'a>(
    env: &'a TypeEnv,
    ty: &'a Type,
    input_expr: &str,
    output_var: &str,
    direction: ConversionDirection,
) -> RcDoc<'a> {
    let converter = Converter::new(env, direction);
    let statement = converter.convert(ty, input_expr, output_var);

    let renderer = AstRenderer::new(env);
    renderer.render_statement(&statement)
}

// Helper functions for the specific conversion directions
pub fn typescript_to_candid<'a>(
    env: &'a TypeEnv,
    ty: &'a Type,
    input_expr: &str,
    output_var: &str,
) -> RcDoc<'a> {
    convert_between_types(
        env,
        ty,
        input_expr,
        output_var,
        ConversionDirection::ToCandid,
    )
}

pub fn candid_to_typescript<'a>(
    env: &'a TypeEnv,
    ty: &'a Type,
    input_expr: &str,
    output_var: &str,
) -> RcDoc<'a> {
    convert_between_types(
        env,
        ty,
        input_expr,
        output_var,
        ConversionDirection::ToTypeScript,
    )
}

// Adapter functions to replace the original functions
pub fn fn_convert_typescript_to_candid<'a>(
    env: &'a TypeEnv,
    arg_id: usize,
    ty: &'a Type,
    context: &'a str,
) -> RcDoc<'a> {
    let input_expr = if context.is_empty() {
        format!("arg{}", arg_id)
    } else {
        format!("{}.arg{}", context, arg_id)
    };

    let output_var = if context.is_empty() {
        format!("_arg{}", arg_id)
    } else {
        format!("{}._arg{}", context, arg_id)
    };

    typescript_to_candid(env, ty, &input_expr, &output_var)
}

pub fn fn_convert_candid_to_typescript<'a>(
    env: &'a TypeEnv,
    result_id: usize,
    ty: &'a Type,
    context: &'a str,
) -> RcDoc<'a> {
    let input_expr = if context.is_empty() {
        format!("_result{}", result_id)
    } else {
        format!("{}._result{}", context, result_id)
    };

    let output_var = if context.is_empty() {
        format!("result{}", result_id)
    } else {
        format!("{}.result{}", context, result_id)
    };

    candid_to_typescript(env, ty, &input_expr, &output_var)
}

// Updated function wrapper generator using the new conversion infrastructure
pub fn generate_function_wrapper<'a>(
    env: &'a TypeEnv,
    func: &'a Function,
    method_name: &'a str,
) -> RcDoc<'a> {
    // Generate parameter conversions (TypeScript -> Candid)
    let param_conversions = func
        .args
        .iter()
        .enumerate()
        .map(|(i, ty)| fn_convert_typescript_to_candid(env, i, ty, ""));

    // Join parameter conversions with newlines
    let param_conversions_doc = RcDoc::intersperse(param_conversions, RcDoc::line());

    // Generate the function call with converted arguments
    let arg_names = (0..func.args.len()).map(|i| str("_arg").append(RcDoc::as_string(i)));
    let args_list = RcDoc::intersperse(arg_names, str(", "));

    // Generate result conversion (Candid -> TypeScript)
    let return_conversion = match func.rets.len() {
        0 => str("return;"),
        1 => {
            let conversion = fn_convert_candid_to_typescript(env, 0, &func.rets[0], "");
            str("const _result0 = await this._actor.")
                .append(str(method_name))
                .append(str("("))
                .append(args_list)
                .append(str(");"))
                .append(RcDoc::line())
                .append(conversion)
                .append(RcDoc::line())
                .append(str("return result0;"))
        }
        _ => {
            // Handle multi-value returns
            let result_decl = str("const [")
                .append(RcDoc::intersperse(
                    (0..func.rets.len()).map(|i| str("_result").append(RcDoc::as_string(i))),
                    str(", "),
                ))
                .append(str("] = await this._actor."))
                .append(str(method_name))
                .append(str("("))
                .append(args_list.clone())
                .append(str(");"));

            let result_conversions = func
                .rets
                .iter()
                .enumerate()
                .map(|(i, ty)| fn_convert_candid_to_typescript(env, i, ty, ""));

            let return_statement = str("return [")
                .append(RcDoc::intersperse(
                    (0..func.rets.len()).map(|i| str("result").append(RcDoc::as_string(i))),
                    str(", "),
                ))
                .append(str("];"));

            result_decl
                .append(RcDoc::line())
                .append(RcDoc::intersperse(result_conversions, RcDoc::line()))
                .append(RcDoc::line())
                .append(return_statement)
        }
    };

    // Combine all parts into the function wrapper
    param_conversions_doc
        .append(RcDoc::line())
        .append(return_conversion)
}
