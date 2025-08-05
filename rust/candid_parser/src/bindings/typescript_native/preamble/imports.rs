use swc_core::common::{SyntaxContext, DUMMY_SP};
use swc_core::ecma::ast::*;

pub fn add_create_actor_imports_and_interface(module: &mut Module) {
    // Add import declaration for types from "@dfinity/agent"
    let import_decl = generate_agent_imports();
    module
        .body
        .push(ModuleItem::ModuleDecl(ModuleDecl::Import(import_decl)));

    let create_actor_options_interface = generate_create_actor_options_interface();
    module
        .body
        .push(ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl {
            span: DUMMY_SP,
            decl: Decl::TsInterface(create_actor_options_interface),
        })));

    // Add CreateActorOptions interface declaration
}

fn generate_agent_imports() -> ImportDecl {
    ImportDecl {
        span: DUMMY_SP,
        specifiers: vec![
            ImportSpecifier::Named(ImportNamedSpecifier {
                span: DUMMY_SP,
                local: Ident::new("ActorCallError".into(), DUMMY_SP, SyntaxContext::empty()),
                imported: None,
                is_type_only: false,
            }),
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
    }
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
