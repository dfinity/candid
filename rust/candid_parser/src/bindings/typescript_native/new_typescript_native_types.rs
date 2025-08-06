use super::super::javascript::is_tuple;
use super::utils::{get_ident_guarded, get_ident_guarded_keyword_ok};
use candid::types::{Field, Function, Label, Type, TypeEnv, TypeInner};
use std::collections::HashMap;

use swc_core::common::{SyntaxContext, DUMMY_SP};
use swc_core::ecma::ast::*;

// Helper function to determine if a type is recursively optional
pub fn is_recursive_optional(
    env: &TypeEnv,
    ty: &Type,
    visited: &mut std::collections::HashSet<String>,
) -> bool {
    use TypeInner::*;

    match ty.as_ref() {
        Var(id) => {
            if !visited.insert(id.clone()) {
                // We've seen this type before, it's recursive
                return true;
            }

            if let Ok(inner_type) = env.find_type(id) {
                is_recursive_optional(env, inner_type, visited)
            } else {
                false
            }
        }
        Opt(inner) => {
            // If we have an optional type, check its inner type
            if let Var(id) = inner.as_ref() {
                if visited.contains(id) {
                    // Found recursive optional
                    return true;
                }
            }
            is_recursive_optional(env, inner, visited)
        }
        _ => false,
    }
}

// Create TS interface from Candid service
pub fn create_interface_from_service(
    enum_declarations: &mut HashMap<Vec<Field>, (TsEnumDecl, String)>,
    env: &TypeEnv,
    id: &str,
    serv: &[(String, Type)],
) -> TsInterfaceDecl {
    let members = serv
        .iter()
        .map(|(method_id, method_ty)| match method_ty.as_ref() {
            TypeInner::Func(ref func) => {
                create_method_signature(enum_declarations, env, method_id, func)
            }
            TypeInner::Var(ref id) => TsTypeElement::TsPropertySignature(TsPropertySignature {
                span: DUMMY_SP,
                key: Box::new(Expr::Ident(get_ident_guarded(method_id))),
                computed: false,
                optional: false,
                readonly: false,
                type_ann: Some(Box::new(TsTypeAnn {
                    span: DUMMY_SP,
                    type_ann: Box::new(TsType::TsTypeRef(TsTypeRef {
                        span: DUMMY_SP,
                        type_name: TsEntityName::Ident(get_ident_guarded(id)),
                        type_params: None,
                    })),
                })),
            }),
            _ => unreachable!(),
        })
        .collect();

    TsInterfaceDecl {
        span: DUMMY_SP,
        declare: false,
        id: get_ident_guarded(&format!("{}Interface", id)),
        type_params: None,
        extends: vec![],
        body: TsInterfaceBody {
            span: DUMMY_SP,
            body: members,
        },
    }
}

// Convert Candid type to TypeScript type
pub fn convert_type(
    enum_declarations: &mut HashMap<Vec<Field>, (TsEnumDecl, String)>,
    env: &TypeEnv,
    ty: &Type,
    is_ref: bool,
) -> TsType {
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
                    convert_type(enum_declarations, env, ty, false)
                } else {
                    TsType::TsTypeRef(TsTypeRef {
                        span: DUMMY_SP,
                        type_name: TsEntityName::Ident(get_ident_guarded(id)),
                        type_params: None,
                    })
                }
            } else {
                TsType::TsTypeRef(TsTypeRef {
                    span: DUMMY_SP,
                    type_name: TsEntityName::Ident(get_ident_guarded(id)),
                    type_params: None,
                })
            }
        }
        // Optional types
        Opt(ref t) => create_opt_type(enum_declarations, env, t, is_ref),
        // Vector types
        Vec(ref t) => create_vector_type(enum_declarations, env, t, is_ref),
        // Record types
        Record(ref fs) => create_record_type(enum_declarations, env, ty, fs, is_ref),
        // Variant types
        Variant(ref fs) => create_variant_type(enum_declarations, env, fs, None),
        Func(_) => create_function_type_ref(),
        // Note: we map to a generic principal type for now
        // see https://github.com/dfinity/candid/issues/606
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

// Internal functions

fn create_opt_type(
    enum_declarations: &mut HashMap<Vec<Field>, (TsEnumDecl, String)>,
    env: &TypeEnv,
    t: &Type,
    is_ref: bool,
) -> TsType {
    use TypeInner::*;
    match t.as_ref() {
        Opt(_) => {
            // Use Some<T> | None for nested optionals
            TsType::TsUnionOrIntersectionType(TsUnionOrIntersectionType::TsUnionType(TsUnionType {
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
                            params: vec![Box::new(convert_type(enum_declarations, env, t, is_ref))],
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
            }))
        }
        Var(id) => {
            // Check for recursion
            let is_recursive = if let Ok(inner_type) = env.find_type(id) {
                let mut visited = std::collections::HashSet::new();
                is_recursive_optional(env, inner_type, &mut visited)
            } else {
                false
            };

            if is_recursive {
                // Use Some<T> | None for recursive optionals
                TsType::TsUnionOrIntersectionType(TsUnionOrIntersectionType::TsUnionType(
                    TsUnionType {
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
                                    params: vec![Box::new(convert_type(
                                        enum_declarations,
                                        env,
                                        t,
                                        is_ref,
                                    ))],
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
                    },
                ))
            } else {
                // Use T | null for non-recursive optionals with Var
                TsType::TsUnionOrIntersectionType(TsUnionOrIntersectionType::TsUnionType(
                    TsUnionType {
                        span: DUMMY_SP,
                        types: vec![
                            Box::new(convert_type(enum_declarations, env, t, is_ref)),
                            Box::new(TsType::TsKeywordType(TsKeywordType {
                                span: DUMMY_SP,
                                kind: TsKeywordTypeKind::TsNullKeyword,
                            })),
                        ],
                    },
                ))
            }
        }
        _ => {
            // Use T | null for simple optionals
            TsType::TsUnionOrIntersectionType(TsUnionOrIntersectionType::TsUnionType(TsUnionType {
                span: DUMMY_SP,
                types: vec![
                    Box::new(convert_type(enum_declarations, env, t, is_ref)),
                    Box::new(TsType::TsKeywordType(TsKeywordType {
                        span: DUMMY_SP,
                        kind: TsKeywordTypeKind::TsNullKeyword,
                    })),
                ],
            }))
        }
    }
}

fn create_vector_type(
    enum_declarations: &mut HashMap<Vec<Field>, (TsEnumDecl, String)>,
    env: &TypeEnv,
    t: &Type,
    is_ref: bool,
) -> TsType {
    use TypeInner::*;
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
                    params: vec![Box::new(convert_type(enum_declarations, env, t, is_ref))],
                })),
            })
        }
    }
}

fn create_record_type(
    enum_declarations: &mut HashMap<Vec<Field>, (TsEnumDecl, String)>,
    env: &TypeEnv,
    ty: &Type,
    fs: &[Field],
    is_ref: bool,
) -> TsType {
    if is_tuple(ty) {
        // Create tuple type
        TsType::TsTupleType(TsTupleType {
            span: DUMMY_SP,
            elem_types: fs
                .iter()
                .map(|f| TsTupleElement {
                    span: DUMMY_SP,
                    label: None,
                    ty: Box::new(convert_type(enum_declarations, env, &f.ty, is_ref)),
                })
                .collect(),
        })
    } else {
        // Create record type
        TsType::TsTypeLit(TsTypeLit {
            span: DUMMY_SP,
            members: fs
                .iter()
                .map(|f| create_property_signature(enum_declarations, env, f))
                .collect(),
        })
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

fn create_variant_type(
    enum_declarations: &mut HashMap<Vec<Field>, (TsEnumDecl, String)>,
    env: &TypeEnv,
    fs: &[Field],
    type_name: Option<&str>,
) -> TsType {
    if fs.is_empty() {
        TsType::TsKeywordType(TsKeywordType {
            span: DUMMY_SP,
            kind: TsKeywordTypeKind::TsNeverKeyword,
        })
    } else {
        // Check if all variants have the same type (especially null)
        let all_null = fs.iter().all(|f| matches!(f.ty.as_ref(), TypeInner::Null));

        if all_null {
            // Only create enum if it doesn't already exist
            enum_declarations.entry(fs.to_vec()).or_insert_with(|| {
                let enum_name = if let Some(name) = type_name {
                    name.to_string()
                } else {
                    // Generate stable name based on field names for inline variants
                    let field_names: Vec<String> = fs
                        .iter()
                        .map(|f| match &*f.id {
                            Label::Named(name) => name.clone(),
                            Label::Id(n) | Label::Unnamed(n) => format!("_{}_", n),
                        })
                        .collect();
                    format!("Variant_{}", field_names.join("_"))
                };
                // Create enum members
                let members = fs
                    .iter()
                    .map(|f| {
                        let member_name = match &*f.id {
                            Label::Named(name) => name.clone(),
                            Label::Id(n) | Label::Unnamed(n) => format!("_{}_", n),
                        };

                        TsEnumMember {
                            span: DUMMY_SP,
                            id: TsEnumMemberId::Ident(get_ident_guarded(&member_name)),
                            init: Some(Box::new(Expr::Lit(Lit::Str(Str {
                                span: DUMMY_SP,
                                value: member_name.into(),
                                raw: None,
                            })))),
                        }
                    })
                    .collect();

                // Create the enum declaration
                let enum_decl = TsEnumDecl {
                    span: DUMMY_SP,
                    declare: false,
                    is_const: false,
                    id: get_ident_guarded(&enum_name),
                    members,
                };

                // Store the enum declaration with its name as key
                (enum_decl, enum_name.clone())
            });

            let enum_name = enum_declarations.get(&fs.to_vec()).unwrap().1.clone();

            // Return a reference to the enum type
            TsType::TsTypeRef(TsTypeRef {
                span: DUMMY_SP,
                type_name: TsEntityName::Ident(get_ident_guarded(&enum_name)),
                type_params: None,
            })
        } else {
            // Create discriminated union with __kind__ field
            TsType::TsUnionOrIntersectionType(TsUnionOrIntersectionType::TsUnionType(TsUnionType {
                span: DUMMY_SP,
                types: fs
                    .iter()
                    .map(|f| {
                        let field_name = match &*f.id {
                            Label::Named(name) => name.clone(),
                            Label::Id(n) | Label::Unnamed(n) => format!("_{}_", n),
                        };
                        
                        // Create the __kind__ property
                        let kind_prop = TsTypeElement::TsPropertySignature(TsPropertySignature {
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
                                        value: field_name.clone().into(),
                                        raw: None,
                                    }),
                                })),
                            })),
                        });
                        
                        // Create the value property
                        let value_prop = create_property_signature_for_variant(
                            enum_declarations,
                            env,
                            f,
                        );
                        
                        Box::new(TsType::TsTypeLit(TsTypeLit {
                            span: DUMMY_SP,
                            members: vec![kind_prop, value_prop],
                        }))
                    })
                    .collect(),
            }))
        }
    }
}

// Add all type definitions from the environment
pub fn add_type_definitions(
    enum_declarations: &mut HashMap<Vec<Field>, (TsEnumDecl, String)>,
    env: &TypeEnv,
    module: &mut Module,
) {
    for id in env.0.keys() {
        if let Ok(ty) = env.find_type(id) {
            match ty.as_ref() {
                TypeInner::Record(_) if !is_tuple(ty) => {
                    // Generate interface for record types
                    let interface = create_interface_from_record(enum_declarations, env, id, ty);
                    module
                        .body
                        .push(ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl {
                            span: DUMMY_SP,
                            decl: Decl::TsInterface(Box::new(interface)),
                        })));
                }
                TypeInner::Service(ref serv) => {
                    // Generate interface for service types
                    let interface = create_interface_from_service(enum_declarations, env, id, serv);
                    module
                        .body
                        .push(ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl {
                            span: DUMMY_SP,
                            decl: Decl::TsInterface(Box::new(interface)),
                        })));
                }
                TypeInner::Func(ref func) => {
                    // Generate type alias for function types
                    let type_alias =
                        create_type_alias_from_function(enum_declarations, env, id, func);
                    module
                        .body
                        .push(ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl {
                            span: DUMMY_SP,
                            decl: Decl::TsTypeAlias(Box::new(type_alias)),
                        })));
                }
                TypeInner::Variant(ref fs) => {
                    // Check if all variants have null type
                    let all_null = fs.iter().all(|f| matches!(f.ty.as_ref(), TypeInner::Null));

                    if all_null {
                        // For variants with all null types, directly create the enum
                        // Don't create a type alias
                        create_variant_type(enum_declarations, env, fs, Some(id));
                    } else {
                        // For other variants, create a type alias to the union type
                        let variant_type =
                            create_variant_type(enum_declarations, env, fs, Some(id));
                        let type_alias = TsTypeAliasDecl {
                            span: DUMMY_SP,
                            declare: false,
                            id: get_ident_guarded(id),
                            type_params: None,
                            type_ann: Box::new(variant_type),
                        };
                        module
                            .body
                            .push(ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl {
                                span: DUMMY_SP,
                                decl: Decl::TsTypeAlias(Box::new(type_alias)),
                            })));
                    }
                }
                TypeInner::Var(ref inner_id) => {
                    let inner_type = env.rec_find_type(inner_id).unwrap();
                    let inner_name = match inner_type.as_ref() {
                        TypeInner::Service(_) => format!("{}Interface", inner_id),
                        _ => inner_id.clone(),
                    };
                    let type_alias = TsTypeAliasDecl {
                        span: DUMMY_SP,
                        declare: false,
                        id: get_ident_guarded(id),
                        type_params: None,
                        type_ann: Box::new(TsType::TsTypeRef(TsTypeRef {
                            span: DUMMY_SP,
                            type_name: TsEntityName::Ident(get_ident_guarded(&inner_name)),
                            type_params: None,
                        })),
                    };
                    module
                        .body
                        .push(ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl {
                            span: DUMMY_SP,
                            decl: Decl::TsTypeAlias(Box::new(type_alias)),
                        })));
                }
                _ => {
                    // Generate type alias for other types
                    let type_alias = create_type_alias(enum_declarations, env, id, ty);
                    module
                        .body
                        .push(ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl {
                            span: DUMMY_SP,
                            decl: Decl::TsTypeAlias(Box::new(type_alias)),
                        })));
                }
            }
        }
    }
}

// Create TS interface from Candid record
fn create_interface_from_record(
    enum_declarations: &mut HashMap<Vec<Field>, (TsEnumDecl, String)>,
    env: &TypeEnv,
    id: &str,
    ty: &Type,
) -> TsInterfaceDecl {
    let members = if let TypeInner::Record(ref fields) = ty.as_ref() {
        fields
            .iter()
            .map(|field| create_property_signature(enum_declarations, env, field))
            .collect()
    } else {
        vec![]
    };

    TsInterfaceDecl {
        span: DUMMY_SP,
        declare: false,
        id: get_ident_guarded(id),
        type_params: None,
        extends: vec![],
        body: TsInterfaceBody {
            span: DUMMY_SP,
            body: members,
        },
    }
}

// Create TS type alias from Candid function
fn create_type_alias_from_function(
    enum_declarations: &mut HashMap<Vec<Field>, (TsEnumDecl, String)>,
    env: &TypeEnv,
    id: &str,
    func: &Function,
) -> TsTypeAliasDecl {
    TsTypeAliasDecl {
        span: DUMMY_SP,
        declare: false,
        id: get_ident_guarded(id),
        type_params: None,
        type_ann: Box::new(create_function_type(enum_declarations, env, func)),
    }
}

// Create general TS type alias
fn create_type_alias(
    enum_declarations: &mut HashMap<Vec<Field>, (TsEnumDecl, String)>,
    env: &TypeEnv,
    id: &str,
    ty: &Type,
) -> TsTypeAliasDecl {
    TsTypeAliasDecl {
        span: DUMMY_SP,
        declare: false,
        id: get_ident_guarded(id),
        type_params: None,
        type_ann: Box::new(convert_type(enum_declarations, env, ty, false)),
    }
}

// Create TS property signature from Candid field
fn create_property_signature(
    enum_declarations: &mut HashMap<Vec<Field>, (TsEnumDecl, String)>,
    env: &TypeEnv,
    field: &Field,
) -> TsTypeElement {
    let field_name = match &*field.id {
        Label::Named(str) => Box::new(Expr::Ident(get_ident_guarded_keyword_ok(str))),
        Label::Id(n) | Label::Unnamed(n) => Box::new(Expr::Ident(Ident::new(
            format!("_{}_", n).into(),
            DUMMY_SP,
            SyntaxContext::empty(),
        ))),
    };

    // Check if the field type is optional
    let (is_optional, type_ann) = if let TypeInner::Opt(ref inner_type) = field.ty.as_ref() {
        (true, convert_type(enum_declarations, env, inner_type, true))
    } else {
        (false, convert_type(enum_declarations, env, &field.ty, true))
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

// Create TS property signature from Candid field
fn create_property_signature_for_variant(
    enum_declarations: &mut HashMap<Vec<Field>, (TsEnumDecl, String)>,
    env: &TypeEnv,
    field: &Field,
) -> TsTypeElement {
    let field_name = match &*field.id {
        Label::Named(str) => Box::new(Expr::Ident(get_ident_guarded_keyword_ok(str))),
        Label::Id(n) | Label::Unnamed(n) => Box::new(Expr::Ident(Ident::new(
            format!("_{}_", n).into(),
            DUMMY_SP,
            SyntaxContext::empty(),
        ))),
    };

    // Check if the field type is optional
    let (is_optional, type_ann) = if let TypeInner::Opt(ref inner_type) = field.ty.as_ref() {
        (true, convert_type(enum_declarations, env, inner_type, true))
    } else {
        (false, convert_type(enum_declarations, env, &field.ty, true))
    };

    let type_ann = if is_optional {
        TsType::TsUnionOrIntersectionType(TsUnionOrIntersectionType::TsUnionType(TsUnionType {
            span: DUMMY_SP,
            types: vec![
                Box::new(type_ann),
                Box::new(TsType::TsKeywordType(TsKeywordType {
                    span: DUMMY_SP,
                    kind: TsKeywordTypeKind::TsNullKeyword,
                })),
            ],
        }))
    } else {
        type_ann
    };

    TsTypeElement::TsPropertySignature(TsPropertySignature {
        span: DUMMY_SP,
        readonly: false,
        key: field_name,
        computed: false,
        optional: false,
        type_ann: Some(Box::new(TsTypeAnn {
            span: DUMMY_SP,
            type_ann: Box::new(type_ann),
        })),
    })
}

// Create TS method signature from Candid function
fn create_method_signature(
    enum_declarations: &mut HashMap<Vec<Field>, (TsEnumDecl, String)>,
    env: &TypeEnv,
    method_id: &str,
    func: &Function,
) -> TsTypeElement {
    // Create parameters
    let params = func
        .args
        .iter()
        .enumerate()
        .map(|(i, arg_ty)| {
            let var_name = arg_ty.name.clone().unwrap_or_else(|| format!("arg{}", i));
            TsFnParam::Ident(BindingIdent {
                id: Ident::new(var_name.into(), DUMMY_SP, SyntaxContext::empty()),
                type_ann: Some(Box::new(TsTypeAnn {
                    span: DUMMY_SP,
                    type_ann: Box::new(convert_type(enum_declarations, env, &arg_ty.typ, true)),
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
        1 => convert_type(enum_declarations, env, &func.rets[0], true),
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
                        ty: Box::new(convert_type(enum_declarations, env, ty, true)),
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
        key: Box::new(Expr::Ident(get_ident_guarded(method_id))),
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
fn create_function_type(
    enum_declarations: &mut HashMap<Vec<Field>, (TsEnumDecl, String)>,
    env: &TypeEnv,
    func: &Function,
) -> TsType {
    // Create parameters
    let params = func
        .args
        .iter()
        .enumerate()
        .map(|(i, arg_ty)| {
            let var_name = arg_ty.name.clone().unwrap_or_else(|| format!("arg{}", i));
            TsFnParam::Ident(BindingIdent {
                id: Ident::new(var_name.into(), DUMMY_SP, SyntaxContext::empty()),
                type_ann: Some(Box::new(TsTypeAnn {
                    span: DUMMY_SP,
                    type_ann: Box::new(convert_type(enum_declarations, env, &arg_ty.typ, true)),
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
        1 => convert_type(enum_declarations, env, &func.rets[0], true),
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
                        ty: Box::new(convert_type(enum_declarations, env, ty, true)),
                    })
                    .collect(),
            })
        }
    };

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

    TsType::TsFnOrConstructorType(TsFnOrConstructorType::TsFnType(TsFnType {
        span: DUMMY_SP,
        params,
        type_params: None,
        type_ann: Box::new(TsTypeAnn {
            span: DUMMY_SP,
            type_ann: Box::new(promise_return_type),
        }),
    }))
}

// Note: we map to a generic function, which is specified by Principal and function name
// see https://github.com/dfinity/candid/issues/606
fn create_function_type_ref() -> TsType {
    // Function references are represented as [Principal, string]
    TsType::TsTupleType(TsTupleType {
        span: DUMMY_SP,
        elem_types: vec![
            TsType::TsTypeRef(TsTypeRef {
                span: DUMMY_SP,
                type_name: TsEntityName::Ident(Ident::new(
                    "Principal".into(),
                    DUMMY_SP,
                    SyntaxContext::empty(),
                )),
                type_params: None,
            }),
            TsType::TsKeywordType(TsKeywordType {
                span: DUMMY_SP,
                kind: TsKeywordTypeKind::TsStringKeyword,
            }),
        ]
        .into_iter()
        .map(|t| TsTupleElement {
            span: DUMMY_SP,
            label: None,
            ty: Box::new(t),
        })
        .collect(),
    })
}
