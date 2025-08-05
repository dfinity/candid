use super::super::javascript::is_tuple;
use super::generate_wrapper::{convert_multi_return_from_candid, TypeConverter};
use super::ident::{contains_unicode_characters, get_ident_guarded, get_ident_guarded_keyword_ok};
use super::preamble::actor::{
    create_canister_id_assignment, create_canister_id_declaration, generate_create_actor_function,
    generate_create_actor_function_declaration,
};
use super::preamble::imports::add_create_actor_imports_and_interface;
use super::preamble::options::{add_option_helpers_interface, add_option_helpers_wrapper};
use candid::types::{Field, Function, Label, Type, TypeEnv, TypeInner};
use std::collections::HashMap;
use swc_core::common::comments::SingleThreadedComments;
use swc_core::common::source_map::SourceMap;
use swc_core::common::sync::Lrc;
use swc_core::common::{SyntaxContext, DUMMY_SP};
use swc_core::ecma::ast::*;
use swc_core::ecma::codegen::{text_writer::JsWriter, Config, Emitter};

pub fn compile(env: &TypeEnv, actor: &Option<Type>, service_name: &str, target: &str) -> String {
    let cm = Lrc::new(SourceMap::default());
    let comments = SingleThreadedComments::default();

    let enum_declarations: &mut HashMap<Vec<Field>, (TsEnumDecl, String)> = &mut HashMap::new();

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

    add_type_definitions(enum_declarations, env, &mut module);

    add_create_actor_imports_and_interface(&mut module);

    // createActor declaration / function
    if target == "interface" {
        let create_actor_fn = generate_create_actor_function_declaration(service_name);
        module
            .body
            .push(ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl {
                span: DUMMY_SP,
                decl: Decl::Var(Box::new(create_actor_fn)),
            })));

        let create_canister_id = create_canister_id_declaration();
        module.body.push(create_canister_id);
    }

    if target == "wrapper" && actor.is_some() {
        let create_actor_fn = generate_create_actor_function(service_name);
        module
            .body
            .push(ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl {
                span: DUMMY_SP,
                decl: Decl::Fn(create_actor_fn),
            })));
        let create_canister_id = create_canister_id_assignment();
        module.body.push(create_canister_id);
    }

    if let Some(actor_type) = actor {
        let mut converter = TypeConverter::new(env, enum_declarations);
        add_actor_implementation(
            env,
            &mut module,
            actor_type,
            service_name,
            target,
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
            module.body.push(ModuleItem::Stmt(stmt.clone()));
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

// Add standard imports
fn add_imports(module: &mut Module, service_name: &str) {
    let dashed_name = service_name.replace('-', "_");

    // Import Actor
    module
        .body
        .push(ModuleItem::ModuleDecl(ModuleDecl::Import(ImportDecl {
            span: DUMMY_SP,
            specifiers: vec![
                ImportSpecifier::Named(ImportNamedSpecifier {
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
                }),
                ImportSpecifier::Named(ImportNamedSpecifier {
                    span: DUMMY_SP,
                    local: Ident::new("_createActor".into(), DUMMY_SP, SyntaxContext::empty()),
                    imported: Some(ModuleExportName::Ident(Ident::new(
                        "createActor".into(),
                        DUMMY_SP,
                        SyntaxContext::empty(),
                    ))),
                    is_type_only: false,
                }),
                ImportSpecifier::Named(ImportNamedSpecifier {
                    span: DUMMY_SP,
                    local: Ident::new("_canisterId".into(), DUMMY_SP, SyntaxContext::empty()),
                    imported: Some(ModuleExportName::Ident(Ident::new(
                        "canisterId".into(),
                        DUMMY_SP,
                        SyntaxContext::empty(),
                    ))),
                    is_type_only: false,
                }),
            ],
            src: Box::new(Str {
                span: DUMMY_SP,
                value: format!("declarations/{}", dashed_name).into(),
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
                value: format!("declarations/{}/{}.did.d.js", dashed_name, dashed_name).into(),
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
fn add_type_definitions(
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

// Create TS interface from Candid service
fn create_interface_from_service(
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
        Opt(ref t) => {
            match t.as_ref() {
                Opt(_) => {
                    // Use Some<T> | None for nested optionals
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
                            params: vec![Box::new(convert_type(enum_declarations, env, t, is_ref))],
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
        // Variant types
        Variant(ref fs) => create_variant_type(enum_declarations, env, fs, None),
        // Note: we map to a generic function, which is specified by Principal and function name
        // see https://github.com/dfinity/candid/issues/606
        Func(_) => {
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
            // Create union of object types (original behavior)
            TsType::TsUnionOrIntersectionType(TsUnionOrIntersectionType::TsUnionType(TsUnionType {
                span: DUMMY_SP,
                types: fs
                    .iter()
                    .map(|f| {
                        Box::new(TsType::TsTypeLit(TsTypeLit {
                            span: DUMMY_SP,
                            members: vec![create_property_signature_for_variant(
                                enum_declarations,
                                env,
                                f,
                            )],
                        }))
                    })
                    .collect(),
            }))
        }
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
    converter: &mut TypeConverter,
) {
    match actor_type.as_ref() {
        TypeInner::Service(ref serv) => {
            add_actor_service_implementation(env, module, serv, service_name, target, converter)
        }
        TypeInner::Var(id) => {
            add_actor_var_implementation(env, module, id, service_name, target, converter)
        }
        TypeInner::Class(_, t) => {
            add_actor_implementation(env, module, t, service_name, target, converter)
        }
        _ => {}
    }
}

// Add actor implementation from service definition

/// Add actor implementation from service definition
fn add_actor_service_implementation(
    env: &TypeEnv,
    module: &mut Module,
    serv: &[(String, Type)],
    service_name: &str,
    target: &str,
    converter: &mut TypeConverter,
) {
    let interface =
        create_interface_from_service(converter.enum_declarations_mut(), env, service_name, serv);
    module
        .body
        .push(ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl {
            span: DUMMY_SP,
            decl: Decl::TsInterface(Box::new(interface)),
        })));

    if target == "wrapper" {
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

// Add actor implementation from a type reference
fn add_actor_var_implementation(
    env: &TypeEnv,
    module: &mut Module,
    type_id: &str,
    service_name: &str,
    target: &str,
    converter: &mut TypeConverter,
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
            span: DUMMY_SP,
            decl: Decl::TsInterface(Box::new(interface)),
        })));
    if target == "wrapper" {
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
}

// Create actor class with methods
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

// Create a class method for an actor function
pub fn create_actor_method(
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
