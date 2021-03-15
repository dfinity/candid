use ic_cdk::export::candid::{check_prog, IDLProg, TypeEnv, CandidType, Deserialize};

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

#[ic_cdk_macros::query]
fn did_to_js(prog: String) -> Option<String> {
    let ast = prog.parse::<IDLProg>().ok()?;
    let mut env = TypeEnv::new();
    let actor = check_prog(&mut env, &ast).ok()?;
    let res = ic_cdk::export::candid::bindings::javascript::compile(&env, &actor);
    Some(res)
}

fn retrieve(path: &str) -> Option<&'static [u8]> {
    match path {
        "/index.html" | "/" => Some(include_bytes!("../../dist/didjs/index.html")),
        "/favicon.ico" => Some(include_bytes!("../../build/favicon.ico")),
        "/index.js" => Some(include_bytes!("../../dist/didjs/index.js")),
        _ => None,
    }
}
struct Uri<'a> {
    path: &'a str,
    params: Vec<&'a str>,
}
fn parse_url(url: &str) -> Uri {
    if let Some(ind) = url.find('?') {
        let (path, rest) = url.split_at(ind);
        let params = rest[1..].split('&').collect();
        Uri { path, params }
    } else {
        Uri { path: url, params: Vec::new() }
    }
}
fn get_path(url: &str) -> Option<&str> {
    url.split('?').next()
}

#[ic_cdk_macros::query]
fn http_request(request: HttpRequest) -> HttpResponse {
    //let url = parse_url(&request.url);
    /*let canister_id = url.params.iter().find_map(|p| if p.starts_with("id=") { Some(&p[3..]) } else { None });
    if canister_id.is_none() {
        return HttpResponse {
            status_code: 400,
            headers: Vec::new(),
            body: b"missing id= parameter".to_vec(),
        }
    }*/
    //let path = url.path;
    let path = get_path(request.url.as_str()).unwrap_or("/");
    if let Some(bytes) = retrieve(path) {
        HttpResponse {
            status_code: 200,
            headers: vec![
                //HeaderField("Content-Encoding".to_string(), "gzip".to_string()),
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
