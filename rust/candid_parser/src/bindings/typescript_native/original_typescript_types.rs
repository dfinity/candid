use candid::types::{Field, Label, Type, TypeEnv, TypeInner};
use candid::types::internal::TypeKey;
use std::collections::HashSet;
use swc_core::common::{SyntaxContext, DUMMY_SP};
use swc_core::ecma::ast::*;

use super::utils::get_ident_guarded_keyword_ok;

pub struct OriginalTypescriptTypes<'a> {
    env: &'a TypeEnv,
    required_candid_imports: HashSet<String>,
}

impl<'a> OriginalTypescriptTypes<'a> {
    pub fn new(env: &'a TypeEnv) -> Self {
        Self {
            env,
            required_candid_imports: HashSet::new(),
        }
    }

    /// Determines if a record structure is a tuple (all fields are numbered or unnamed).
    fn is_tuple(&mut self, fields: &[Field]) -> bool {
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

    fn get_required_candid_imports(&self) -> &HashSet<String> {
        &self.required_candid_imports
    }

    fn add_required_import(&mut self, type_id: &str) {
        // print the type_id
        self.required_candid_imports.insert(type_id.to_string());
    }

    fn create_var_type(&mut self, id: &TypeKey) -> TsType {
        let ty = self.env.rec_find_type(id).unwrap();
        if matches!(ty.as_ref(), TypeInner::Func(_)) {
            return self.create_inline_actor_method();
        }
        if matches!(ty.as_ref(), TypeInner::Service(_)) {
            return self.create_inline_service();
        }
        // For named types, use the imported Candid type
        self.add_required_import(id.as_str());
        TsType::TsTypeRef(TsTypeRef {
            span: DUMMY_SP,
            type_name: TsEntityName::Ident(Ident::new(
                format!("_{}", id.as_str()).into(),
                DUMMY_SP,
                SyntaxContext::empty(),
            )),
            type_params: None,
        })
    }

    /// Converts a Candid type to a TypeScript type for return values.
    /// This function generates TypeScript types that match the output of `pp_ty` in the
    /// candid-ts printer module.
    ///
    /// The key difference from parameter types is the representation of optionals and tuples.
    fn create_type(&mut self, ty: &Type) -> TsType {
        match ty.as_ref() {
            TypeInner::Var(id) => self.create_var_type(id),
            TypeInner::Opt(inner) => {
                // For Option types, return "[] | [T]" to match pp_ty output
                TsType::TsUnionOrIntersectionType(TsUnionOrIntersectionType::TsUnionType(
                    TsUnionType {
                        span: DUMMY_SP,
                        types: vec![
                            // [] (empty array comes first to match pp_ty)
                            Box::new(TsType::TsTupleType(TsTupleType {
                                span: DUMMY_SP,
                                elem_types: vec![],
                            })),
                            // [T]
                            Box::new(TsType::TsTupleType(TsTupleType {
                                span: DUMMY_SP,
                                elem_types: vec![TsTupleElement {
                                    span: DUMMY_SP,
                                    label: None,
                                    ty: Box::new(self.create_type_ref(inner)),
                                }],
                            })),
                        ],
                    },
                ))
            }
            TypeInner::Record(fields) => {
                if self.is_tuple(fields) {
                    // Create a properly typed tuple matching pp_ty's output format: [T1, T2, ...]
                    TsType::TsTupleType(TsTupleType {
                        span: DUMMY_SP,
                        elem_types: fields
                            .iter()
                            .map(|field| TsTupleElement {
                                span: DUMMY_SP,
                                label: None,
                                ty: Box::new(self.create_type_ref(&field.ty)),
                            })
                            .collect(),
                    })
                } else {
                    // Create record type with same structure but with converted field types
                    TsType::TsTypeLit(TsTypeLit {
                        span: DUMMY_SP,
                        members: fields
                            .iter()
                            .map(|field| {
                                let field_name = match &*field.id {
                                    Label::Named(name) => name.clone(),
                                    Label::Id(n) | Label::Unnamed(n) => format!("_{}_", n),
                                };

                                let field_type = match field.ty.as_ref() {
                                    TypeInner::Opt(inner) => {
                                        // For optional fields, create union "[] | [T]" to match pp_ty
                                        TsType::TsUnionOrIntersectionType(
                                            TsUnionOrIntersectionType::TsUnionType(TsUnionType {
                                                span: DUMMY_SP,
                                                types: vec![
                                                    // [] (empty array first)
                                                    Box::new(TsType::TsTupleType(TsTupleType {
                                                        span: DUMMY_SP,
                                                        elem_types: vec![],
                                                    })),
                                                    // [T]
                                                    Box::new(TsType::TsTupleType(TsTupleType {
                                                        span: DUMMY_SP,
                                                        elem_types: vec![TsTupleElement {
                                                            span: DUMMY_SP,
                                                            label: None,
                                                            ty: Box::new(
                                                                self.create_type_ref(inner),
                                                            ),
                                                        }],
                                                    })),
                                                ],
                                            }),
                                        )
                                    }
                                    _ => self.create_type_ref(&field.ty),
                                };

                                TsTypeElement::TsPropertySignature(TsPropertySignature {
                                    span: DUMMY_SP,
                                    readonly: false,
                                    key: Box::new(Expr::Ident(Ident::new(
                                        field_name.into(),
                                        DUMMY_SP,
                                        SyntaxContext::empty(),
                                    ))),
                                    computed: false,
                                    optional: false,
                                    type_ann: Some(Box::new(TsTypeAnn {
                                        span: DUMMY_SP,
                                        type_ann: Box::new(field_type),
                                    })),
                                })
                            })
                            .collect(),
                    })
                }
            }
            TypeInner::Null => TsType::TsKeywordType(TsKeywordType {
                span: DUMMY_SP,
                kind: TsKeywordTypeKind::TsNullKeyword,
            }),
            TypeInner::Bool => TsType::TsKeywordType(TsKeywordType {
                span: DUMMY_SP,
                kind: TsKeywordTypeKind::TsBooleanKeyword,
            }),
            TypeInner::Nat | TypeInner::Int | TypeInner::Nat64 | TypeInner::Int64 => {
                TsType::TsKeywordType(TsKeywordType {
                    span: DUMMY_SP,
                    kind: TsKeywordTypeKind::TsBigIntKeyword,
                })
            }
            TypeInner::Nat8
            | TypeInner::Nat16
            | TypeInner::Nat32
            | TypeInner::Int8
            | TypeInner::Int16
            | TypeInner::Int32
            | TypeInner::Float32
            | TypeInner::Float64 => TsType::TsKeywordType(TsKeywordType {
                span: DUMMY_SP,
                kind: TsKeywordTypeKind::TsNumberKeyword,
            }),
            TypeInner::Text => TsType::TsKeywordType(TsKeywordType {
                span: DUMMY_SP,
                kind: TsKeywordTypeKind::TsStringKeyword,
            }),
            // Special types
            TypeInner::Reserved => TsType::TsKeywordType(TsKeywordType {
                span: DUMMY_SP,
                kind: TsKeywordTypeKind::TsAnyKeyword,
            }),
            TypeInner::Empty => TsType::TsKeywordType(TsKeywordType {
                span: DUMMY_SP,
                kind: TsKeywordTypeKind::TsNeverKeyword,
            }),
            TypeInner::Principal => TsType::TsTypeRef(TsTypeRef {
                span: DUMMY_SP,
                type_name: TsEntityName::Ident(Ident::new(
                    "Principal".into(),
                    DUMMY_SP,
                    SyntaxContext::empty(),
                )),
                type_params: None,
            }),
            // Vector types
            TypeInner::Vec(ref t) => {
                let ty = match t.as_ref() {
                    TypeInner::Var(ref id) => {
                        let ty = self.env.rec_find_type(id).unwrap();
                        if matches!(
                            ty.as_ref(),
                            TypeInner::Nat8
                                | TypeInner::Nat16
                                | TypeInner::Nat32
                                | TypeInner::Nat64
                                | TypeInner::Int8
                                | TypeInner::Int16
                                | TypeInner::Int32
                                | TypeInner::Int64
                        ) {
                            ty
                        } else {
                            t
                        }
                    }
                    _ => t,
                };

                match ty.as_ref() {
                    TypeInner::Nat8 => self.create_union_array_type("Uint8Array", "number"),
                    TypeInner::Nat16 => self.create_union_array_type("Uint16Array", "number"),
                    TypeInner::Nat32 => self.create_union_array_type("Uint32Array", "number"),
                    TypeInner::Nat64 => self.create_union_array_type("BigUint64Array", "bigint"),
                    TypeInner::Int8 => self.create_union_array_type("Int8Array", "number"),
                    TypeInner::Int16 => self.create_union_array_type("Int16Array", "number"),
                    TypeInner::Int32 => self.create_union_array_type("Int32Array", "number"),
                    TypeInner::Int64 => self.create_union_array_type("BigInt64Array", "bigint"),
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
                                params: vec![Box::new(self.get_type(ty))],
                            })),
                        })
                    }
                }
            }

            // Variant types
            TypeInner::Variant(ref fs) => {
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
                                        members: vec![self.create_property_signature(f)],
                                    }))
                                })
                                .collect(),
                        },
                    ))
                }
            }

            TypeInner::Func(_) => self.create_inline_actor_method(),
            TypeInner::Service(_) => self.create_inline_service(),
            // Unsupported types
            TypeInner::Class(_, _)
            | TypeInner::Knot(_)
            | TypeInner::Unknown
            | TypeInner::Future => TsType::TsKeywordType(TsKeywordType {
                span: DUMMY_SP,
                kind: TsKeywordTypeKind::TsAnyKeyword,
            }),
        }
    }

    fn create_inline_service(&mut self) -> TsType {
        TsType::TsTypeRef(TsTypeRef {
            span: DUMMY_SP,
            type_name: TsEntityName::Ident(Ident::new(
                "Principal".into(),
                DUMMY_SP,
                SyntaxContext::empty(),
            )),
            type_params: None,
        })
    }

    fn create_inline_actor_method(&mut self) -> TsType {
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

    fn create_union_array_type(&mut self, typed_array: &str, elem_type: &str) -> TsType {
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

    fn create_property_signature(&mut self, field: &Field) -> TsTypeElement {
        let field_name = match &*field.id {
            Label::Named(str) => Box::new(Expr::Ident(get_ident_guarded_keyword_ok(str))),
            Label::Id(n) | Label::Unnamed(n) => Box::new(Expr::Ident(Ident::new(
                format!("_{}_", n).into(),
                DUMMY_SP,
                SyntaxContext::empty(),
            ))),
        };

        TsTypeElement::TsPropertySignature(TsPropertySignature {
            span: DUMMY_SP,
            readonly: false,
            key: field_name,
            computed: false,
            optional: false,
            type_ann: Some(Box::new(TsTypeAnn {
                span: DUMMY_SP,
                type_ann: Box::new(self.get_type(&field.ty)),
            })),
        })
    }

    /// Helper function that handles references to types by name.
    /// For named types (TypeInner::Var), it creates a type reference.
    /// For other types, it defers to create_type.
    fn create_type_ref(&mut self, ty: &Type) -> TsType {
        match ty.as_ref() {
            TypeInner::Var(id) => self.create_var_type(id),
            _ => {
                // For anonymous types, use a detailed structure
                self.create_type(ty)
            }
        }
    }

    pub fn get_type(&mut self, ty: &Type) -> TsType {
        match ty.as_ref() {
            TypeInner::Record(_) | TypeInner::Variant(_) => {
                // For records and variants, use the imported Candid type if available
                self.create_type_ref(ty)
            }
            _ => self.create_type(ty),
        }
    }

    pub fn add_import_for_original_type_definitions(
        &mut self,
        module: &mut Module,
        service_name: &str,
    ) {
        // Use the collected required imports instead of passed-in types
        let required_imports = self.get_required_candid_imports();
        if required_imports.is_empty() {
            return;
        }

        let dashed_name = service_name.replace('-', "_");

        // Create import specifiers for each type
        let specifiers = required_imports
            .iter()
            .map(|id| {
                ImportSpecifier::Named(ImportNamedSpecifier {
                    span: DUMMY_SP,
                    local: Ident::new(format!("_{}", id).into(), DUMMY_SP, SyntaxContext::empty()),
                    imported: Some(ModuleExportName::Ident(Ident::new(
                        id.clone().into(),
                        DUMMY_SP,
                        SyntaxContext::empty(),
                    ))),
                    is_type_only: false,
                })
            })
            .collect::<Vec<_>>();

        // Sort specifiers by name
        let mut sorted_specifiers = specifiers;
        sorted_specifiers.sort_by(|a, b| {
            let a_name = match a {
                ImportSpecifier::Named(spec) => spec.local.sym.to_string(),
                ImportSpecifier::Default(spec) => spec.local.sym.to_string(),
                ImportSpecifier::Namespace(spec) => spec.local.sym.to_string(),
            };

            let b_name = match b {
                ImportSpecifier::Named(spec) => spec.local.sym.to_string(),
                ImportSpecifier::Default(spec) => spec.local.sym.to_string(),
                ImportSpecifier::Namespace(spec) => spec.local.sym.to_string(),
            };

            a_name.cmp(&b_name)
        });

        // Add import declaration
        module
            .body
            .push(ModuleItem::ModuleDecl(ModuleDecl::Import(ImportDecl {
                span: DUMMY_SP,
                specifiers: sorted_specifiers,
                src: Box::new(Str {
                    span: DUMMY_SP,
                    value: format!("declarations/{}/{}.did.d.ts", dashed_name, dashed_name).into(),
                    raw: None,
                }),
                type_only: true,
                with: None,
                phase: Default::default(),
            })));
    }
}
