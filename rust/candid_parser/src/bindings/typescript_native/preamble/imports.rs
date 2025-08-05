use swc_core::common::{SyntaxContext, DUMMY_SP};
use swc_core::ecma::ast::*;

pub fn interface_imports(module: &mut Module) {
    interface_dfinity_agent_imports(module);
    dfinity_principal_import(module);
}

pub fn wrapper_imports(module: &mut Module, service_name: &str) {
    wrapper_dfinity_agent_imports(module);
    dfinity_principal_import(module);
    old_bindings_imports(module, service_name);
}

fn old_bindings_imports(module: &mut Module, service_name: &str) {
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

pub fn interface_create_actor_options(module: &mut Module) {
    let create_actor_options_interface = generate_create_actor_options_interface();
    module
        .body
        .push(ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl {
            span: DUMMY_SP,
            decl: Decl::TsInterface(create_actor_options_interface),
        })));
}

fn dfinity_principal_import(module: &mut Module) {
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

fn interface_dfinity_agent_imports(module: &mut Module) {
    let import_decl = ImportDecl {
        span: DUMMY_SP,
        specifiers: vec![
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
    };
    module
        .body
        .push(ModuleItem::ModuleDecl(ModuleDecl::Import(import_decl)));
}

fn wrapper_dfinity_agent_imports(module: &mut Module) {
    let import_decl = ImportDecl {
        span: DUMMY_SP,
        specifiers: vec![
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
            ImportSpecifier::Named(ImportNamedSpecifier {
                span: DUMMY_SP,
                local: Ident::new("ActorSubclass".into(), DUMMY_SP, SyntaxContext::empty()),
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
    };
    module
        .body
        .push(ModuleItem::ModuleDecl(ModuleDecl::Import(import_decl)));
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
