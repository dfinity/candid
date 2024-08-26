use base64::engine::general_purpose::STANDARD as BASE64;
use base64::Engine;
use candid::types::{subtype, Type, TypeInner};
use candid_parser::{check_prog, IDLProg, TypeEnv};
use ic_asset_certification::{
    Asset, AssetConfig, AssetEncoding, AssetFallbackConfig, AssetRedirectKind, AssetRouter,
};
use ic_cdk::{
    api::{data_certificate, set_certified_data},
    *,
};
use ic_certification::HashTree;
use ic_http_certification::{HeaderField, HttpCertificationTree, HttpRequest, HttpResponse};
use include_dir::{include_dir, Dir};
use serde::Serialize;
use std::{cell::RefCell, rc::Rc};

thread_local! {
    static HTTP_TREE: Rc<RefCell<HttpCertificationTree>> = Default::default();

    // initializing the asset router with an HTTP certification tree is optional.
    // if direct access to the HTTP certification tree is not needed for certifying
    // requests and responses outside of the asset router, then this step can be skipped.
    static ASSET_ROUTER: RefCell<AssetRouter<'static>> = RefCell::new(AssetRouter::with_tree(HTTP_TREE.with(|tree| tree.clone())));
}

static ASSETS_DIR: Dir<'_> = include_dir!("$CARGO_MANIFEST_DIR/../../dist/didjs/");
const IMMUTABLE_ASSET_CACHE_CONTROL: &str = "public, max-age=31536000, immutable";

#[ic_cdk::query]
fn did_to_js(prog: String) -> Option<String> {
    let ast = prog.parse::<IDLProg>().ok()?;
    let mut env = TypeEnv::new();
    let actor = check_prog(&mut env, &ast).ok()?;
    let res = candid_parser::bindings::javascript::compile(&env, &actor);
    Some(res)
}

#[ic_cdk::query]
fn binding(prog: String, lang: String) -> Option<String> {
    use candid_parser::bindings;
    let ast = prog.parse::<IDLProg>().ok()?;
    let mut env = TypeEnv::new();
    let actor = check_prog(&mut env, &ast).ok()?;
    let res = match lang.as_str() {
        "ts" => bindings::typescript::compile(&env, &actor),
        "mo" => bindings::motoko::compile(&env, &actor),
        "installed_did" => {
            let actor = actor.and_then(|t: Type| {
                let t = env.trace_type(&t).ok()?;
                if let TypeInner::Class(_, ty) = t.as_ref() {
                    Some(ty.clone())
                } else {
                    Some(t)
                }
            });
            candid::pretty::candid::compile(&env, &actor)
        }
        _ => return None,
    };
    Some(res)
}

#[ic_cdk::query]
fn merge_init_args(prog: String, init_args: String) -> Option<String> {
    let (env, actor) = candid_parser::utils::merge_init_args(&prog, &init_args).ok()?;
    Some(candid::pretty::candid::compile(&env, &Some(actor)))
}

#[ic_cdk::query]
fn subtype(new: String, old: String) -> Result<(), String> {
    let new = new.parse::<IDLProg>().unwrap();
    let old = old.parse::<IDLProg>().unwrap();
    let mut new_env = TypeEnv::new();
    let mut old_env = TypeEnv::new();
    let new_actor = check_prog(&mut new_env, &new).unwrap().unwrap();
    let old_actor = check_prog(&mut old_env, &old).unwrap().unwrap();
    let mut gamma = std::collections::HashSet::new();
    let old_actor = new_env.merge_type(old_env, old_actor);
    subtype::subtype(&mut gamma, &new_env, &new_actor, &old_actor).map_err(|e| e.to_string())
}

#[init]
fn init() {
    certify_all_assets();
}

#[post_upgrade]
fn post_upgrade() {
    init();
}

#[query]
fn http_request(req: HttpRequest) -> HttpResponse {
    serve_asset(&req)
}

/// Rescursively collect all assets from the provided directory
fn collect_assets<'content, 'path>(
    dir: &'content Dir<'path>,
    assets: &mut Vec<Asset<'content, 'path>>,
) {
    for file in dir.files() {
        assets.push(Asset::new(file.path().to_string_lossy(), file.contents()));
    }

    for dir in dir.dirs() {
        collect_assets(dir, assets);
    }
}

// Certification
fn certify_all_assets() {
    // 1. Define the asset certification configurations.
    let encodings = vec![
        AssetEncoding::Brotli.default_config(),
        AssetEncoding::Gzip.default_config(),
    ];

    let asset_configs = vec![
        AssetConfig::File {
            path: "index.html".to_string(),
            content_type: Some("text/html".to_string()),
            headers: get_asset_headers(vec![(
                "cache-control".to_string(),
                "public, no-cache, no-store".to_string(),
            )]),
            fallback_for: vec![AssetFallbackConfig {
                scope: "/".to_string(),
            }],
            aliased_by: vec!["/".to_string()],
            encodings: encodings.clone(),
        },
        AssetConfig::Pattern {
            pattern: "**/*.js".to_string(),
            content_type: Some("text/javascript".to_string()),
            headers: get_asset_headers(vec![(
                "cache-control".to_string(),
                IMMUTABLE_ASSET_CACHE_CONTROL.to_string(),
            )]),
            encodings: encodings.clone(),
        },
        AssetConfig::Pattern {
            pattern: "**/*.css".to_string(),
            content_type: Some("text/css".to_string()),
            headers: get_asset_headers(vec![(
                "cache-control".to_string(),
                IMMUTABLE_ASSET_CACHE_CONTROL.to_string(),
            )]),
            encodings,
        },
        AssetConfig::Pattern {
            pattern: "**/*.ico".to_string(),
            content_type: Some("image/x-icon".to_string()),
            headers: get_asset_headers(vec![(
                "cache-control".to_string(),
                IMMUTABLE_ASSET_CACHE_CONTROL.to_string(),
            )]),
            encodings: vec![],
        },
        AssetConfig::Pattern {
            pattern: "**/*.svg".to_string(),
            content_type: Some("image/svg+xml".to_string()),
            headers: get_asset_headers(vec![(
                "cache-control".to_string(),
                IMMUTABLE_ASSET_CACHE_CONTROL.to_string(),
            )]),
            encodings: vec![],
        },
        AssetConfig::Redirect {
            from: "/old-url".to_string(),
            to: "/".to_string(),
            kind: AssetRedirectKind::Permanent,
        },
    ];

    // 2. Collect all assets from the frontend build directory.
    let mut assets = Vec::new();
    collect_assets(&ASSETS_DIR, &mut assets);

    ASSET_ROUTER.with_borrow_mut(|asset_router| {
        // 3. Certify the assets using the `certify_assets` function from the `ic-asset-certification` crate.
        if let Err(err) = asset_router.certify_assets(assets, asset_configs) {
            ic_cdk::trap(&format!("Failed to certify assets: {}", err));
        }

        // 4. Set the canister's certified data.
        set_certified_data(&asset_router.root_hash());
    });
}

// Handlers
fn serve_asset(req: &HttpRequest) -> HttpResponse {
    ASSET_ROUTER.with_borrow(|asset_router| {
        if let Ok((mut response, witness, expr_path)) = asset_router.serve_asset(req) {
            add_certificate_header(&mut response, &witness, &expr_path);

            response
        } else {
            ic_cdk::trap("Failed to serve asset");
        }
    })
}

fn get_asset_headers(additional_headers: Vec<HeaderField>) -> Vec<HeaderField> {
    // set up the default headers and include additional headers provided by the caller
    let mut headers = vec![
        ("strict-transport-security".to_string(), "max-age=31536000; includeSubDomains".to_string()),
        ("x-frame-options".to_string(), "DENY".to_string()),
        ("x-content-type-options".to_string(), "nosniff".to_string()),
        ("content-security-policy".to_string(), "default-src 'self'; form-action 'self'; object-src 'none'; frame-ancestors 'none'; upgrade-insecure-requests; block-all-mixed-content".to_string()),
        ("referrer-policy".to_string(), "no-referrer".to_string()),
        ("permissions-policy".to_string(), "accelerometer=(),ambient-light-sensor=(),autoplay=(),battery=(),camera=(),display-capture=(),document-domain=(),encrypted-media=(),fullscreen=(),gamepad=(),geolocation=(),gyroscope=(),layout-animations=(self),legacy-image-formats=(self),magnetometer=(),microphone=(),midi=(),oversized-images=(self),payment=(),picture-in-picture=(),publickey-credentials-get=(),speaker-selection=(),sync-xhr=(self),unoptimized-images=(self),unsized-media=(self),usb=(),screen-wake-lock=(),web-share=(),xr-spatial-tracking=()".to_string()),
        ("cross-origin-embedder-policy".to_string(), "require-corp".to_string()),
        ("cross-origin-opener-policy".to_string(), "same-origin".to_string()),
    ];
    headers.extend(additional_headers);

    headers
}

const IC_CERTIFICATE_HEADER: &str = "IC-Certificate";
fn add_certificate_header(response: &mut HttpResponse, witness: &HashTree, expr_path: &[String]) {
    let certified_data = data_certificate().expect("No data certificate available");
    let witness = cbor_encode(witness);
    let expr_path = cbor_encode(&expr_path);

    response.headers.push((
        IC_CERTIFICATE_HEADER.to_string(),
        format!(
            "certificate=:{}:, tree=:{}:, expr_path=:{}:, version=2",
            BASE64.encode(certified_data),
            BASE64.encode(witness),
            BASE64.encode(expr_path)
        ),
    ));
}

// Encoding
fn cbor_encode(value: &impl Serialize) -> Vec<u8> {
    let mut serializer = serde_cbor::Serializer::new(Vec::new());
    serializer
        .self_describe()
        .expect("Failed to self describe CBOR");
    value
        .serialize(&mut serializer)
        .expect("Failed to serialize value");
    serializer.into_inner()
}

ic_cdk::export_candid!();
