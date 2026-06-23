use candid::types::{subtype, Type, TypeInner};
use candid_parser::{check_prog, IDLProg, TypeEnv};
use ic_cdk::api::{
    certified_data_set, data_certificate, root_key,
};
use ic_cdk::{init, post_upgrade};
use ic_http_certification::{
    utils::add_v2_certificate_header, DefaultCelBuilder, DefaultResponseCertification,
    HttpCertification, HttpCertificationPath, HttpCertificationTree, HttpCertificationTreeEntry,
    HttpRequest, HttpResponse, CERTIFICATE_EXPRESSION_HEADER_NAME,
};
use percent_encoding::{utf8_percent_encode, NON_ALPHANUMERIC};
use std::cell::RefCell;
use std::collections::HashMap;

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

#[init]
fn init() {
    certify_all_assets();
}

#[post_upgrade]
fn post_upgrade() {
    init();
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
    let errors = subtype::subtype_check_all(&mut gamma, &new_env, &new_actor, &old_actor);
    if errors.is_empty() {
        Ok(())
    } else {
        let report = subtype::format_report(&errors);
        Err(format!(
            "{} incompatible change{} found:\n\n{report}",
            errors.len(),
            if errors.len() == 1 { "" } else { "s" }
        ))
    }
}

#[ic_cdk::query]
fn http_request(request: HttpRequest) -> HttpResponse<'static> {
    //TODO add /canister_id/ as endpoint when ICQC is available.
    let req_path = request.get_path().unwrap_or_else(|_| "/".to_string());

    // Look up the exact-path response, falling back to the certified 404 wildcard.
    let (tree_path, certified) = RESPONSES.with_borrow(|responses| {
        if let Some(certified) = responses.get(&req_path) {
            (HttpCertificationPath::exact(&req_path), certified.clone())
        } else {
            (
                not_found_tree_path(),
                NOT_FOUND.with_borrow(|n| n.clone().unwrap()),
            )
        }
    });

    let CertifiedHttpResponse {
        mut response,
        certification,
    } = certified;

    HTTP_TREE.with_borrow(|tree| {
        let witness = tree
            .witness(
                &HttpCertificationTreeEntry::new(&tree_path, certification),
                &req_path,
            )
            .unwrap();
        add_v2_certificate_header(
            &data_certificate().expect("No data certificate available"),
            &mut response,
            &witness,
            &tree_path.to_expr_path(),
        );
    });

    response
}

// Storage

// The static assets served by this canister, baked into the wasm at build time.
const INDEX_HTML: &[u8] = include_bytes!("../../dist/didjs/index.html");
const FAVICON: &[u8] = include_bytes!("../../dist/didjs/favicon.ico");
const INDEX_JS: &[u8] = include_bytes!("../../dist/didjs/index.js");

// `/` and `/index.html` both serve the SPA entry point.
const ASSETS: &[(&str, &str, &[u8])] = &[
    ("/", "text/html", INDEX_HTML),
    ("/index.html", "text/html", INDEX_HTML),
    ("/favicon.ico", "image/x-icon", FAVICON),
    ("/index.js", "application/javascript", INDEX_JS),
];

// Body returned (and certified) for any request that doesn't match a known asset.
const NOT_FOUND_BODY: &[u8] = b"Not found";

// A pre-certified response, ready to be served alongside its tree witness.
#[derive(Clone)]
struct CertifiedHttpResponse {
    response: HttpResponse<'static>,
    certification: HttpCertification,
}

thread_local! {
    static HTTP_TREE: RefCell<HttpCertificationTree> = RefCell::new(HttpCertificationTree::default());
    // Exact-path responses, keyed by request path.
    static RESPONSES: RefCell<HashMap<String, CertifiedHttpResponse>> = RefCell::new(HashMap::new());
    // Wildcard fallback served for any unmatched path.
    static NOT_FOUND: RefCell<Option<CertifiedHttpResponse>> = const { RefCell::new(None) };
}

// The `ic_env` cookie carries environment data compatible with the canister environment
// variables cookie. It is only attached to `text/html` responses.
const SET_COOKIE_HEADER_NAME: &str = "Set-Cookie";
const IC_ENV_COOKIE_NAME: &str = "ic_env";

// Builds the (URL-encoded) `ic_env` cookie value
// `ic_root_key=<hex>` and CANISTER_ID, joined by `&`.
fn encoded_canister_env() -> String {
    let values = [
        format!("ic_root_key={}", hex::encode(root_key())),
        format!("CANISTER_ID={}", ic_cdk::api::canister_self()),
    ];

    utf8_percent_encode(&values.join("&"), NON_ALPHANUMERIC).to_string()
}

// Certification

fn build_response(
    status_code: u16,
    content_type: &str,
    body: &'static [u8],
    cel_expr_str: &str,
    encoded_canister_env: &str,
) -> HttpResponse<'static> {
    let mut headers = vec![
        (
            CERTIFICATE_EXPRESSION_HEADER_NAME.to_string(),
            cel_expr_str.to_string(),
        ),
        ("Content-Type".to_string(), content_type.to_string()),
        ("Content-Length".to_string(), format!("{}", body.len())),
        ("Cache-Control".to_string(), format!("max-age={}", 600)),
        (
            "Cross-Origin-Embedder-Policy".to_string(),
            "require-corp".to_string(),
        ),
        (
            "Cross-Origin-Resource-Policy".to_string(),
            "cross-origin".to_string(),
        ),
    ];

    // Attach the canister environment cookie to HTML responses only.
    if content_type == "text/html" {
        headers.push((
            SET_COOKIE_HEADER_NAME.to_string(),
            format!("{IC_ENV_COOKIE_NAME}={encoded_canister_env}; SameSite=Lax"),
        ));
    }

    HttpResponse::builder()
        .with_status_code(status_code)
        .with_headers(headers)
        .with_body(body)
        .build()
}

fn certify_all_assets() {
    let canister_env = encoded_canister_env();

    // We certify the full response (no excluded headers) and exclude the request.
    let cel = DefaultCelBuilder::response_only_certification()
        .with_response_certification(DefaultResponseCertification::response_header_exclusions(
            vec![],
        ))
        .build();
    let cel_str = cel.to_string();

    HTTP_TREE.with_borrow_mut(|tree| {
        // Certify each static asset at its exact path.
        for (path, content_type, body) in ASSETS {
            let response = build_response(200, content_type, body, &cel_str, &canister_env);
            let certification = HttpCertification::response_only(&cel, &response, None).unwrap();
            let tree_path = HttpCertificationPath::exact(*path);
            tree.insert(&HttpCertificationTreeEntry::new(&tree_path, certification));
            RESPONSES.with_borrow_mut(|responses| {
                responses.insert(
                    path.to_string(),
                    CertifiedHttpResponse {
                        response,
                        certification,
                    },
                );
            });
        }

        // Certify a 404 response under a wildcard path, covering every other request.
        let response = build_response(404, "text/plain", NOT_FOUND_BODY, &cel_str, &canister_env);
        let certification = HttpCertification::response_only(&cel, &response, None).unwrap();
        tree.insert(&HttpCertificationTreeEntry::new(
            not_found_tree_path(),
            certification,
        ));
        NOT_FOUND.with_borrow_mut(|not_found| {
            *not_found = Some(CertifiedHttpResponse {
                response,
                certification,
            });
        });

        certified_data_set(tree.root_hash());
    });
}

fn not_found_tree_path() -> HttpCertificationPath<'static> {
    HttpCertificationPath::wildcard("")
}

ic_cdk::export_candid!();
