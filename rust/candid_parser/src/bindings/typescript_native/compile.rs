use super::super::javascript::is_tuple;
use super::generate_wrapper::{convert_multi_return_from_candid, TypeConverter};
use super::helper_functions::{add_option_helpers_interface, add_option_helpers_wrapper};
use candid::types::{Field, Function, Label, Type, TypeEnv, TypeInner};
use swc_core::common::comments::SingleThreadedComments;
use swc_core::common::source_map::SourceMap;
use swc_core::common::sync::Lrc;
use swc_core::common::{SyntaxContext, DUMMY_SP};
use swc_core::ecma::ast::*;
use swc_core::ecma::codegen::{text_writer::JsWriter, Config, Emitter};
// Map of JavaScript/TypeScript keywords to escape
static KEYWORDS: [&str; 125] = [
    // Original JavaScript keywords
    "abstract",
    "arguments",
    "await",
    "boolean",
    "break",
    "byte",
    "case",
    "catch",
    "char",
    "class",
    "const",
    "continue",
    "debugger",
    "default",
    "delete",
    "do",
    "double",
    "else",
    "enum",
    "eval",
    "export",
    "extends",
    "false",
    "final",
    "finally",
    "float",
    "for",
    "function",
    "goto",
    "if",
    "implements",
    "import",
    "in",
    "instanceof",
    "int",
    "interface",
    "let",
    "long",
    "native",
    "new",
    "null",
    "package",
    "private",
    "protected",
    "public",
    "return",
    "short",
    "static",
    "super",
    "switch",
    "synchronized",
    "this",
    "throw",
    "throws",
    "transient",
    "true",
    "try",
    "typeof",
    "var",
    "void",
    "volatile",
    "while",
    "with",
    "yield",
    // TypeScript primitive types
    "any",
    "unknown",
    "never",
    "undefined",
    "object",
    "symbol",
    "bigint",
    "number",
    "string",
    // Utility types
    "Partial",
    "Required",
    "Readonly",
    "Record",
    "Pick",
    "Omit",
    "Exclude",
    "Extract",
    "NonNullable",
    "Parameters",
    "ConstructorParameters",
    "ReturnType",
    "InstanceType",
    "ThisParameterType",
    "OmitThisParameter",
    "ThisType",
    "Uppercase",
    "Lowercase",
    "Capitalize",
    "Uncapitalize",
    // Common built-in types/interfaces
    "Array",
    "ReadonlyArray",
    "Function",
    "Date",
    "Error",
    "Promise",
    "Map",
    "Set",
    "WeakMap",
    "WeakSet",
    "Iterator",
    "IterableIterator",
    "Generator",
    "RegExp",
    "ArrayBuffer",
    "DataView",
    "Float32Array",
    "Float64Array",
    "Int8Array",
    "Int16Array",
    "Int32Array",
    "Uint8Array",
    "Uint16Array",
    "Uint32Array",
    "Uint8ClampedArray",
    "BigInt64Array",
    "BigUint64Array",
    // Common global objects
    "Math",
    "JSON",
    "console",
    "document",
    "window",
];

pub fn compile(env: &TypeEnv, actor: &Option<Type>, service_name: &str, target: &str) -> String {
    let cm = Lrc::new(SourceMap::default());
    let comments = SingleThreadedComments::default();

    let mut module = Module {
        span: DUMMY_SP,
        body: vec![],
        shebang: None,
    };

    if target == "wrapper" {
        add_imports(&mut module, service_name);
    }

    add_principal_import(&mut module);
    add_option_helpers_interface(&mut module);

    if target == "wrapper" {
        add_option_helpers_wrapper(&mut module);
    }

    add_type_definitions(env, &mut module);
    if let Some(actor_type) = actor {
        add_actor_implementation(env, &mut module, actor_type, service_name, target);
    }

    // Generate code from the AST
    let mut buf = vec![];
    {
        let writer = JsWriter::new(cm.clone(), "\n", &mut buf, None);
        let mut emitter = Emitter {
            cfg: Config::default().with_minify(false),
            cm: cm.clone(),
            comments: Some(&comments),
            wr: Box::new(writer),
        };

        emitter.emit_module(&module).unwrap();
    }

    String::from_utf8(buf).unwrap()
}

// Ensure identifier is not a reserved keyword
fn create_ident(name: &str) -> Ident {
    let ident_name = if KEYWORDS.contains(&name) {
        format!("{}_", name)
    } else {
        name.to_string()
    };

    Ident::new(ident_name.into(), DUMMY_SP, SyntaxContext::empty())
}

// Add standard imports
fn add_imports(module: &mut Module, service_name: &str) {
    let dashed_name = service_name.replace('-', "_");

    // Import Actor
    module
        .body
        .push(ModuleItem::ModuleDecl(ModuleDecl::Import(ImportDecl {
            span: DUMMY_SP,
            specifiers: vec![ImportSpecifier::Named(ImportNamedSpecifier {
                span: DUMMY_SP,
                local: Ident::new(
                    format!("_{}", service_name).into(),
                    DUMMY_SP,
                    SyntaxContext::empty(),
                ),
                imported: Some(ModuleExportName::Ident(Ident::new(
                    service_name.into(),
                    DUMMY_SP,
                    SyntaxContext::empty(),
                ))),
                is_type_only: false,
            })],
            src: Box::new(Str {
                span: DUMMY_SP,
                value: format!("../../declarations/{}", dashed_name).into(),
                raw: None,
            }),
            type_only: false,
            with: None,
            phase: Default::default(),
        })));

    // Import ActorSubclass
    module
        .body
        .push(ModuleItem::ModuleDecl(ModuleDecl::Import(ImportDecl {
            span: DUMMY_SP,
            specifiers: vec![ImportSpecifier::Named(ImportNamedSpecifier {
                span: DUMMY_SP,
                local: Ident::new("ActorSubclass".into(), DUMMY_SP, SyntaxContext::empty()),
                imported: None,
                is_type_only: true,
            })],
            src: Box::new(Str {
                span: DUMMY_SP,
                value: "@dfinity/agent".into(),
                raw: None,
            }),
            type_only: false,
            with: None,
            phase: Default::default(),
        })));

    // Import _SERVICE
    module
        .body
        .push(ModuleItem::ModuleDecl(ModuleDecl::Import(ImportDecl {
            span: DUMMY_SP,
            specifiers: vec![ImportSpecifier::Named(ImportNamedSpecifier {
                span: DUMMY_SP,
                local: Ident::new("_SERVICE".into(), DUMMY_SP, SyntaxContext::empty()),
                imported: None,
                is_type_only: false,
            })],
            src: Box::new(Str {
                span: DUMMY_SP,
                value: format!(
                    "../../declarations/{}/{}.did.d.js",
                    dashed_name, dashed_name
                )
                .into(),
                raw: None,
            }),
            type_only: false,
            with: None,
            phase: Default::default(),
        })));
}

// Add Principal type import
fn add_principal_import(module: &mut Module) {
    module
        .body
        .push(ModuleItem::ModuleDecl(ModuleDecl::Import(ImportDecl {
            span: DUMMY_SP,
            specifiers: vec![ImportSpecifier::Named(ImportNamedSpecifier {
                span: DUMMY_SP,
                local: Ident::new("Principal".into(), DUMMY_SP, SyntaxContext::empty()),
                imported: None,
                is_type_only: false,
            })],
            src: Box::new(Str {
                span: DUMMY_SP,
                value: "@dfinity/principal".into(),
                raw: None,
            }),
            type_only: true,
            with: None,
            phase: Default::default(),
        })));
}

// Add all type definitions from the environment
fn add_type_definitions(env: &TypeEnv, module: &mut Module) {
    for (id, _) in &env.0 {
        if let Ok(ty) = env.find_type(id) {
            match ty.as_ref() {
                TypeInner::Record(_) if !is_tuple(ty) => {
                    // Generate interface for record types
                    let interface = create_interface_from_record(env, id, ty);
                    module
                        .body
                        .push(ModuleItem::Stmt(Stmt::Decl(Decl::TsInterface(Box::new(
                            interface,
                        )))));
                }
                TypeInner::Service(ref serv) => {
                    // Generate interface for service types
                    let interface = create_interface_from_service(env, id, serv);
                    module
                        .body
                        .push(ModuleItem::Stmt(Stmt::Decl(Decl::TsInterface(Box::new(
                            interface,
                        )))));
                }
                TypeInner::Func(ref func) => {
                    // Generate type alias for function types
                    let type_alias = create_type_alias_from_function(env, id, func);
                    module
                        .body
                        .push(ModuleItem::Stmt(Stmt::Decl(Decl::TsTypeAlias(Box::new(
                            type_alias,
                        )))));
                }
                _ => {
                    // Generate type alias for other types
                    let type_alias = create_type_alias(env, id, ty);
                    module
                        .body
                        .push(ModuleItem::Stmt(Stmt::Decl(Decl::TsTypeAlias(Box::new(
                            type_alias,
                        )))));
                }
            }
        }
    }
}

// Create TS interface from Candid record
fn create_interface_from_record(env: &TypeEnv, id: &str, ty: &Type) -> TsInterfaceDecl {
    let members = if let TypeInner::Record(ref fields) = ty.as_ref() {
        fields
            .iter()
            .map(|field| create_property_signature(env, field))
            .collect()
    } else {
        vec![]
    };

    TsInterfaceDecl {
        span: DUMMY_SP,
        declare: false,
        id: create_ident(id),
        type_params: None,
        extends: vec![],
        body: TsInterfaceBody {
            span: DUMMY_SP,
            body: members,
        },
    }
}

// Create TS interface from Candid service
fn create_interface_from_service(
    env: &TypeEnv,
    id: &str,
    serv: &Vec<(String, Type)>,
) -> TsInterfaceDecl {
    let members = serv
        .iter()
        .map(|(method_id, method_ty)| match method_ty.as_ref() {
            TypeInner::Func(ref func) => create_method_signature(env, method_id, func),
            _ => create_property_signature_from_type(env, method_id, method_ty),
        })
        .collect();

    TsInterfaceDecl {
        span: DUMMY_SP,
        declare: false,
        id: create_ident(id),
        type_params: None,
        extends: vec![],
        body: TsInterfaceBody {
            span: DUMMY_SP,
            body: members,
        },
    }
}

// Create TS type alias from Candid function
fn create_type_alias_from_function(env: &TypeEnv, id: &str, func: &Function) -> TsTypeAliasDecl {
    TsTypeAliasDecl {
        span: DUMMY_SP,
        declare: false,
        id: create_ident(id),
        type_params: None,
        type_ann: Box::new(create_function_type(env, func)),
    }
}

// Create general TS type alias
fn create_type_alias(env: &TypeEnv, id: &str, ty: &Type) -> TsTypeAliasDecl {
    TsTypeAliasDecl {
        span: DUMMY_SP,
        declare: false,
        id: create_ident(id),
        type_params: None,
        type_ann: Box::new(convert_type(env, ty, false)),
    }
}

// Create TS property signature from Candid field
fn create_property_signature(env: &TypeEnv, field: &Field) -> TsTypeElement {
    let field_name = match &*field.id {
        Label::Named(str) => Box::new(Expr::Ident(create_ident(str))),
        Label::Id(n) | Label::Unnamed(n) => Box::new(Expr::Ident(Ident::new(
            format!("_{}_", n).into(),
            DUMMY_SP,
            SyntaxContext::empty(),
        ))),
    };

    // Check if the field type is optional
    let (is_optional, type_ann) = if let TypeInner::Opt(ref inner_type) = field.ty.as_ref() {
        (true, convert_type(env, inner_type, true))
    } else {
        (false, convert_type(env, &field.ty, true))
    };

    TsTypeElement::TsPropertySignature(TsPropertySignature {
        span: DUMMY_SP,
        readonly: false,
        key: field_name,
        computed: false,
        optional: is_optional,
        type_ann: Some(Box::new(TsTypeAnn {
            span: DUMMY_SP,
            type_ann: Box::new(type_ann),
        })),
    })
}

// Create TS property signature from Candid type
fn create_property_signature_from_type(env: &TypeEnv, name: &str, ty: &Type) -> TsTypeElement {
    TsTypeElement::TsPropertySignature(TsPropertySignature {
        span: DUMMY_SP,
        readonly: false,
        key: Box::new(Expr::Ident(create_ident(name))),
        computed: false,
        optional: false,
        type_ann: Some(Box::new(TsTypeAnn {
            span: DUMMY_SP,
            type_ann: Box::new(convert_type(env, ty, true)),
        })),
    })
}

// Create TS method signature from Candid function
fn create_method_signature(env: &TypeEnv, method_id: &str, func: &Function) -> TsTypeElement {
    // Create parameters
    let params = func
        .args
        .iter()
        .enumerate()
        .map(|(i, ty)| {
            TsFnParam::Ident(BindingIdent {
                id: Ident::new(format!("arg{}", i).into(), DUMMY_SP, SyntaxContext::empty()),
                type_ann: Some(Box::new(TsTypeAnn {
                    span: DUMMY_SP,
                    type_ann: Box::new(convert_type(env, ty, true)),
                })),
            })
        })
        .collect();

    // Create return type
    let return_type = match func.rets.len() {
        0 => TsType::TsKeywordType(TsKeywordType {
            span: DUMMY_SP,
            kind: TsKeywordTypeKind::TsVoidKeyword,
        }),
        1 => convert_type(env, &func.rets[0], true),
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
                        ty: Box::new(convert_type(env, ty, true)),
                    })
                    .collect(),
            })
        }
    };

    // Wrap return type in Promise
    let promise_return_type = TsType::TsTypeRef(TsTypeRef {
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
    });

    TsTypeElement::TsMethodSignature(TsMethodSignature {
        span: DUMMY_SP,
        key: Box::new(Expr::Ident(create_ident(method_id))),
        computed: false,
        optional: false,
        params,
        type_ann: Some(Box::new(TsTypeAnn {
            span: DUMMY_SP,
            type_ann: Box::new(promise_return_type),
        })),
        type_params: None,
    })
}

// Create a function type representation
fn create_function_type(env: &TypeEnv, func: &Function) -> TsType {
    // Create parameters
    let params = func
        .args
        .iter()
        .enumerate()
        .map(|(i, ty)| {
            TsFnParam::Ident(BindingIdent {
                id: Ident::new(format!("arg{}", i).into(), DUMMY_SP, SyntaxContext::empty()),
                type_ann: Some(Box::new(TsTypeAnn {
                    span: DUMMY_SP,
                    type_ann: Box::new(convert_type(env, ty, true)),
                })),
            })
        })
        .collect();

    // Create return type
    let return_type = match func.rets.len() {
        0 => TsType::TsKeywordType(TsKeywordType {
            span: DUMMY_SP,
            kind: TsKeywordTypeKind::TsVoidKeyword,
        }),
        1 => convert_type(env, &func.rets[0], true),
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
                        ty: Box::new(convert_type(env, ty, true)),
                    })
                    .collect(),
            })
        }
    };

    TsType::TsFnOrConstructorType(TsFnOrConstructorType::TsFnType(TsFnType {
        span: DUMMY_SP,
        params,
        type_params: None,
        type_ann: Box::new(TsTypeAnn {
            span: DUMMY_SP,
            type_ann: Box::new(return_type),
        }),
    }))
}

// Convert Candid type to TypeScript type
fn convert_type(env: &TypeEnv, ty: &Type, is_ref: bool) -> TsType {
    use TypeInner::*;

    match ty.as_ref() {
        // Primitive types
        Null => TsType::TsKeywordType(TsKeywordType {
            span: DUMMY_SP,
            kind: TsKeywordTypeKind::TsNullKeyword,
        }),
        Bool => TsType::TsKeywordType(TsKeywordType {
            span: DUMMY_SP,
            kind: TsKeywordTypeKind::TsBooleanKeyword,
        }),
        Nat | Int | Nat64 | Int64 => TsType::TsKeywordType(TsKeywordType {
            span: DUMMY_SP,
            kind: TsKeywordTypeKind::TsBigIntKeyword,
        }),
        Nat8 | Nat16 | Nat32 | Int8 | Int16 | Int32 | Float32 | Float64 => {
            TsType::TsKeywordType(TsKeywordType {
                span: DUMMY_SP,
                kind: TsKeywordTypeKind::TsNumberKeyword,
            })
        }
        Text => TsType::TsKeywordType(TsKeywordType {
            span: DUMMY_SP,
            kind: TsKeywordTypeKind::TsStringKeyword,
        }),
        // Special types
        Reserved => TsType::TsKeywordType(TsKeywordType {
            span: DUMMY_SP,
            kind: TsKeywordTypeKind::TsAnyKeyword,
        }),
        Empty => TsType::TsKeywordType(TsKeywordType {
            span: DUMMY_SP,
            kind: TsKeywordTypeKind::TsNeverKeyword,
        }),
        Principal => TsType::TsTypeRef(TsTypeRef {
            span: DUMMY_SP,
            type_name: TsEntityName::Ident(Ident::new(
                "Principal".into(),
                DUMMY_SP,
                SyntaxContext::empty(),
            )),
            type_params: None,
        }),
        // Reference types
        Var(ref id) => {
            if is_ref {
                let ty = env.rec_find_type(id).unwrap();
                if matches!(ty.as_ref(), Service(_) | Func(_)) {
                    convert_type(env, ty, false)
                } else {
                    TsType::TsTypeRef(TsTypeRef {
                        span: DUMMY_SP,
                        type_name: TsEntityName::Ident(create_ident(id)),
                        type_params: None,
                    })
                }
            } else {
                TsType::TsTypeRef(TsTypeRef {
                    span: DUMMY_SP,
                    type_name: TsEntityName::Ident(create_ident(id)),
                    type_params: None,
                })
            }
        }
        // Optional types
        Opt(ref t) => {
            match t.as_ref() {
                Opt(_) => {
                    // Use Option<T> for nested optionals
                    TsType::TsTypeRef(TsTypeRef {
                        span: DUMMY_SP,
                        type_name: TsEntityName::Ident(Ident::new(
                            "Option".into(),
                            DUMMY_SP,
                            SyntaxContext::empty(),
                        )),
                        type_params: Some(Box::new(TsTypeParamInstantiation {
                            span: DUMMY_SP,
                            params: vec![Box::new(convert_type(env, t, is_ref))],
                        })),
                    })
                }
                _ => {
                    // Use T | null for simple optionals
                    TsType::TsUnionOrIntersectionType(TsUnionOrIntersectionType::TsUnionType(
                        TsUnionType {
                            span: DUMMY_SP,
                            types: vec![
                                Box::new(convert_type(env, t, is_ref)),
                                Box::new(TsType::TsKeywordType(TsKeywordType {
                                    span: DUMMY_SP,
                                    kind: TsKeywordTypeKind::TsNullKeyword,
                                })),
                            ],
                        },
                    ))
                }
            }
        }
        // Vector types
        Vec(ref t) => {
            let ty = match t.as_ref() {
                Var(ref id) => {
                    let ty = env.rec_find_type(id).unwrap();
                    if matches!(
                        ty.as_ref(),
                        Nat8 | Nat16 | Nat32 | Nat64 | Int8 | Int16 | Int32 | Int64
                    ) {
                        ty
                    } else {
                        t
                    }
                }
                _ => t,
            };

            match ty.as_ref() {
                Nat8 => create_union_array_type("Uint8Array", "number"),
                Nat16 => create_union_array_type("Uint16Array", "number"),
                Nat32 => create_union_array_type("Uint32Array", "number"),
                Nat64 => create_union_array_type("BigUint64Array", "bigint"),
                Int8 => create_union_array_type("Int8Array", "number"),
                Int16 => create_union_array_type("Int16Array", "number"),
                Int32 => create_union_array_type("Int32Array", "number"),
                Int64 => create_union_array_type("BigInt64Array", "bigint"),
                _ => {
                    // Generic array type
                    TsType::TsTypeRef(TsTypeRef {
                        span: DUMMY_SP,
                        type_name: TsEntityName::Ident(Ident::new(
                            "Array".into(),
                            DUMMY_SP,
                            SyntaxContext::empty(),
                        )),
                        type_params: Some(Box::new(TsTypeParamInstantiation {
                            span: DUMMY_SP,
                            params: vec![Box::new(convert_type(env, t, is_ref))],
                        })),
                    })
                }
            }
        }
        // Record types
        Record(ref fs) => {
            if is_tuple(ty) {
                // Create tuple type
                TsType::TsTupleType(TsTupleType {
                    span: DUMMY_SP,
                    elem_types: fs
                        .iter()
                        .map(|f| TsTupleElement {
                            span: DUMMY_SP,
                            label: None,
                            ty: Box::new(convert_type(env, &f.ty, is_ref)),
                        })
                        .collect(),
                })
            } else {
                // Create record type
                TsType::TsTypeLit(TsTypeLit {
                    span: DUMMY_SP,
                    members: fs
                        .iter()
                        .map(|f| create_property_signature(env, f))
                        .collect(),
                })
            }
        }
        // Variant types
        Variant(ref fs) => {
            if fs.is_empty() {
                TsType::TsKeywordType(TsKeywordType {
                    span: DUMMY_SP,
                    kind: TsKeywordTypeKind::TsNeverKeyword,
                })
            } else {
                // Create union of object types
                TsType::TsUnionOrIntersectionType(TsUnionOrIntersectionType::TsUnionType(
                    TsUnionType {
                        span: DUMMY_SP,
                        types: fs
                            .iter()
                            .map(|f| {
                                Box::new(TsType::TsTypeLit(TsTypeLit {
                                    span: DUMMY_SP,
                                    members: vec![create_property_signature(env, f)],
                                }))
                            })
                            .collect(),
                    },
                ))
            }
        }
        // Function types
        Func(ref func) => create_function_type(env, func),
        // Service types
        Service(_) => TsType::TsTypeRef(TsTypeRef {
            span: DUMMY_SP,
            type_name: TsEntityName::Ident(Ident::new(
                "Principal".into(),
                DUMMY_SP,
                SyntaxContext::empty(),
            )),
            type_params: None,
        }),
        // Unsupported types
        Class(_, _) | Knot(_) | Unknown | Future => TsType::TsKeywordType(TsKeywordType {
            span: DUMMY_SP,
            kind: TsKeywordTypeKind::TsAnyKeyword,
        }),
    }
}

// Helper to create union array types like "Uint8Array | number[]"
fn create_union_array_type(typed_array: &str, elem_type: &str) -> TsType {
    TsType::TsUnionOrIntersectionType(TsUnionOrIntersectionType::TsUnionType(TsUnionType {
        span: DUMMY_SP,
        types: vec![
            // TypedArray (e.g., Uint8Array)
            Box::new(TsType::TsTypeRef(TsTypeRef {
                span: DUMMY_SP,
                type_name: TsEntityName::Ident(Ident::new(
                    typed_array.into(),
                    DUMMY_SP,
                    SyntaxContext::empty(),
                )),
                type_params: None,
            })),
            // Regular array (e.g., number[])
            Box::new(TsType::TsArrayType(TsArrayType {
                span: DUMMY_SP,
                elem_type: Box::new(TsType::TsKeywordType(TsKeywordType {
                    span: DUMMY_SP,
                    kind: match elem_type {
                        "number" => TsKeywordTypeKind::TsNumberKeyword,
                        "bigint" => TsKeywordTypeKind::TsBigIntKeyword,
                        _ => TsKeywordTypeKind::TsAnyKeyword,
                    },
                })),
            })),
        ],
    }))
}

// Add actor implementation
fn add_actor_implementation(
    env: &TypeEnv,
    module: &mut Module,
    actor_type: &Type,
    service_name: &str,
    target: &str,
) {
    match actor_type.as_ref() {
        TypeInner::Service(ref serv) => {
            add_actor_service_implementation(env, module, serv, service_name, target)
        }
        TypeInner::Var(id) => add_actor_var_implementation(env, module, id, service_name, target),
        TypeInner::Class(_, t) => add_actor_implementation(env, module, t, service_name, target),
        _ => {}
    }
}

// Add actor implementation from service definition
fn add_actor_service_implementation(
    env: &TypeEnv,
    module: &mut Module,
    serv: &Vec<(String, Type)>,
    service_name: &str,
    target: &str,
) {
    let interface = create_interface_from_service(env, service_name, serv);
    module
        .body
        .push(ModuleItem::Stmt(Stmt::Decl(Decl::TsInterface(Box::new(
            interface,
        )))));

    if target == "wrapper" {
        let class_decl = create_actor_class(env, service_name, serv);
        module
            .body
            .push(ModuleItem::Stmt(Stmt::Decl(Decl::Class(class_decl))));
    }
}

// Add actor implementation from a type reference
fn add_actor_var_implementation(
    env: &TypeEnv,
    module: &mut Module,
    type_id: &str,
    service_name: &str,
    target: &str,
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
        id: create_ident(service_name),
        type_params: None,
        extends: vec![TsExprWithTypeArgs {
            span: DUMMY_SP,
            expr: Box::new(Expr::Ident(create_ident(type_id))),
            type_args: None,
        }],
        body: TsInterfaceBody {
            span: DUMMY_SP,
            body: vec![],
        },
    };
    module
        .body
        .push(ModuleItem::Stmt(Stmt::Decl(Decl::TsInterface(Box::new(
            interface,
        )))));

    if target == "wrapper" {
        // Then add the implementation class
        let class_decl = create_actor_class(env, service_name, serv);
        module
            .body
            .push(ModuleItem::Stmt(Stmt::Decl(Decl::Class(class_decl))));
    }
}

// Create actor class with methods
fn create_actor_class(env: &TypeEnv, service_name: &str, serv: &Vec<(String, Type)>) -> ClassDecl {
    // Create private actor field
    let actor_field = ClassMember::PrivateProp(PrivateProp {
        span: DUMMY_SP,
        key: PrivateName {
            span: DUMMY_SP,
            name: "actor".into(),
        },
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
        accessibility: None,
        is_static: false,
        decorators: vec![],
        ctxt: SyntaxContext::empty(),
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
        params: vec![],
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
                        prop: MemberProp::PrivateName(PrivateName {
                            span: DUMMY_SP,
                            name: "actor".into(),
                        }),
                    })),
                    right: Box::new(Expr::Ident(Ident::new(
                        format!("_{}", service_name).into(),
                        DUMMY_SP,
                        SyntaxContext::empty(),
                    ))),
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
                Some(create_actor_method(env, method_id, func))
            } else {
                None
            }
        })
        .collect();

    // Combine all members
    let mut members = vec![actor_field, constructor];
    members.extend(methods);

    ClassDecl {
        ident: create_ident(service_name),
        declare: false,
        class: Box::new(Class {
            span: DUMMY_SP,
            body: members,
            super_class: None,
            type_params: None,
            super_type_params: None,
            implements: vec![TsExprWithTypeArgs {
                span: DUMMY_SP,
                expr: Box::new(Expr::Ident(create_ident(service_name).into())),
                type_args: None,
            }],
            is_abstract: false,
            decorators: vec![],
            ctxt: SyntaxContext::empty(),
        }),
    }
}

// Create a class method for an actor function
pub fn create_actor_method(env: &TypeEnv, method_id: &str, func: &Function) -> ClassMember {
    // Create type converter
    let converter = TypeConverter::new(env);

    // Create parameters
    let params = func
        .args
        .iter()
        .enumerate()
        .map(|(i, ty)| Param {
            span: DUMMY_SP,
            decorators: vec![],
            pat: Pat::Ident(BindingIdent {
                id: Ident::new(format!("arg{}", i).into(), DUMMY_SP, SyntaxContext::empty()),
                type_ann: Some(Box::new(TsTypeAnn {
                    span: DUMMY_SP,
                    type_ann: Box::new(convert_type(env, ty, true)),
                })),
            }),
        })
        .collect();

    // Create return type
    let return_type = match func.rets.len() {
        0 => TsType::TsKeywordType(TsKeywordType {
            span: DUMMY_SP,
            kind: TsKeywordTypeKind::TsVoidKeyword,
        }),
        1 => convert_type(env, &func.rets[0], true),
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
                        ty: Box::new(convert_type(env, ty, true)),
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
        .map(|(i, ty)| {
            let arg_ident =
                Ident::new(format!("arg{}", i).into(), DUMMY_SP, SyntaxContext::empty());
            let arg_expr = Expr::Ident(arg_ident);

            // Apply type conversion
            let converted_expr = converter.to_candid(&arg_expr, ty);

            ExprOrSpread {
                spread: None,
                expr: Box::new(converted_expr),
            }
        })
        .collect::<Vec<_>>();

    // Create the function call to the actor method
    let actor_call = Expr::Call(CallExpr {
        span: DUMMY_SP,
        callee: Callee::Expr(Box::new(Expr::Member(MemberExpr {
            span: DUMMY_SP,
            obj: Box::new(Expr::Member(MemberExpr {
                span: DUMMY_SP,
                obj: Box::new(Expr::This(ThisExpr { span: DUMMY_SP })),
                prop: MemberProp::PrivateName(PrivateName {
                    span: DUMMY_SP,
                    name: "actor".into(),
                }),
            })),
            prop: MemberProp::Ident(create_ident(method_id).into()),
        }))),
        args: converted_args,
        type_args: None,
        ctxt: SyntaxContext::empty(),
    });

    // Create await expression to call the actor
    let await_expr = Expr::Await(AwaitExpr {
        span: DUMMY_SP,
        arg: Box::new(actor_call),
    });

    // Variable to hold the raw result
    let result_var = Ident::new("result".into(), DUMMY_SP, SyntaxContext::empty());

    // Create result variable declaration
    let result_var_decl = VarDecl {
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
    };

    // Convert the result based on return type(s)
    let converted_result = if func.rets.is_empty() {
        // No return value
        Expr::Ident(result_var)
    } else {
        // Convert the result to the expected TypeScript type
        let result_expr = Expr::Ident(result_var);
        convert_multi_return_from_candid(&converter, &result_expr, &func.rets)
    };

    // Create return statement with converted result
    let return_stmt = ReturnStmt {
        span: DUMMY_SP,
        arg: Some(Box::new(converted_result)),
    };

    // Method body with variable declaration and return statement
    let body_stmts = vec![
        Stmt::Decl(Decl::Var(Box::new(result_var_decl))),
        Stmt::Return(return_stmt),
    ];

    ClassMember::Method(ClassMethod {
        span: DUMMY_SP,
        key: PropName::Ident(create_ident(method_id).into()),
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
