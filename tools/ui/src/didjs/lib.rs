use base64::engine::general_purpose::STANDARD as BASE64;
use base64::Engine;
use candid::types::{subtype, Type, TypeInner};
use candid_parser::{check_prog, CandidType, Deserialize, IDLProg, TypeEnv};
use ic_cdk::api::{data_certificate, set_certified_data};
use ic_cdk::{init, post_upgrade};
use ic_certification::{labeled, leaf, HashTree};
use ic_http_certification::DefaultCelBuilder;
use ic_representation_independent_hash::hash;
use serde::Serialize;

#[derive(CandidType, Deserialize)]
pub struct HeaderField(pub String, pub String);

#[derive(CandidType, Deserialize)]
pub struct HttpRequest {
    pub method: String,
    pub url: String,
    pub headers: Vec<HeaderField>,
    #[serde(with = "serde_bytes")]
    pub body: Vec<u8>,
}

#[derive(CandidType, Deserialize)]
pub struct HttpResponse {
    pub status_code: u16,
    pub headers: Vec<HeaderField>,
    #[serde(with = "serde_bytes")]
    pub body: Vec<u8>,
}

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

fn retrieve(path: &str) -> Option<(&str, &'static [u8])> {
    match path {
        "/index.html" | "/" => Some(("text/html", include_bytes!("../../dist/didjs/index.html"))),
        "/favicon.ico" => Some((
            "image/x-icon",
            include_bytes!("../../dist/didjs/favicon.ico"),
        )),
        "/index.js" => Some((
            "application/javascript",
            include_bytes!("../../dist/didjs/index.js"),
        )),
        _ => None,
    }
}

fn get_path(url: &str) -> Option<&str> {
    url.split('?').next()
}

#[ic_cdk::query]
fn http_request(request: HttpRequest) -> HttpResponse {
    //TODO add /canister_id/ as endpoint when ICQC is available.
    let path = get_path(request.url.as_str()).unwrap_or("/");
    let mut response = if let Some((content_type, bytes)) = retrieve(path) {
        HttpResponse {
            status_code: 200,
            headers: vec![
                HeaderField("Content-Type".to_string(), content_type.to_string()),
                HeaderField("Content-Length".to_string(), format!("{}", bytes.len())),
                HeaderField("Cache-Control".to_string(), format!("max-age={}", 600)),
                HeaderField("Cross-Origin-Embedder-Policy".to_string(), "require-corp".to_string()),
                HeaderField("Cross-Origin-Resource-Policy".to_string(), "cross-origin".to_string()),
            ],
            body: bytes.to_vec(),
        }
    } else {
        HttpResponse {
            status_code: 404,
            headers: Vec::new(),
            body: path.as_bytes().to_vec(),
        }
    };
    add_certification_headers(&mut response);
    response
}

// Certify that frontend asset certification is skipped for this canister.

const IC_CERTIFICATE_HEADER: &str = "IC-Certificate";
const IC_CERTIFICATE_EXPRESSION_HEADER: &str = "IC-CertificateExpression";

fn skip_certification_cel_expr() -> String {
    DefaultCelBuilder::skip_certification().to_string()
}

fn skip_certification_asset_tree() -> HashTree {
    let cel_expr_hash = hash(skip_certification_cel_expr().as_bytes());
    labeled(
        "http_expr",
        labeled("<*>", labeled(cel_expr_hash, leaf(vec![]))),
    )
}

fn add_certification_headers(response: &mut HttpResponse) {
    let certified_data = data_certificate().expect("No data certificate available");
    let witness = cbor_encode(&skip_certification_asset_tree());
    let expr_path = ["http_expr", "<*>"];
    let expr_path = cbor_encode(&expr_path);

    response.headers.push(HeaderField(
        IC_CERTIFICATE_EXPRESSION_HEADER.to_string(),
        skip_certification_cel_expr(),
    ));
    response.headers.push(HeaderField(
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

#[init]
fn init() {
    set_certified_data(&skip_certification_asset_tree().digest());
}

#[post_upgrade]
fn post_upgrade() {
    init();
}

ic_cdk::export_candid!();
