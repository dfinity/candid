use candid::types::{subtype, Type, TypeInner};
use candid_parser::{check_prog, CandidType, Deserialize, IDLProg, TypeEnv};

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
    if let Some((content_type, bytes)) = retrieve(path) {
        HttpResponse {
            status_code: 200,
            headers: vec![
                HeaderField("Content-Type".to_string(), content_type.to_string()),
                HeaderField("Content-Length".to_string(), format!("{}", bytes.len())),
                HeaderField("Cache-Control".to_string(), format!("max-age={}", 600)),
            ],
            body: bytes.to_vec(),
        }
    } else {
        HttpResponse {
            status_code: 404,
            headers: Vec::new(),
            body: path.as_bytes().to_vec(),
        }
    }
}

ic_cdk::export_candid!();
