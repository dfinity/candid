// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
#![allow(dead_code, unused_imports)]
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::api::call::CallResult as Result;

#[derive(CandidType, Deserialize)]
pub struct StreamingToken { pub resource: String, pub index: candid::Nat }
#[derive(CandidType, Deserialize)]
pub struct StreamingCallbackHttpResponse {
  pub token: Option<StreamingToken>,
  pub body: serde_bytes::ByteBuf,
}
#[derive(CandidType, Deserialize)]
pub struct HeaderField (pub String, pub String);
#[derive(CandidType, Deserialize)]
pub struct HttpRequest {
  pub url: String,
  pub method: String,
  pub body: serde_bytes::ByteBuf,
  pub headers: Vec<HeaderField>,
}
candid::define_function!(pub StreamingCallback : (StreamingToken) -> (
    StreamingCallbackHttpResponse,
  ) query);
#[derive(CandidType, Deserialize)]
pub enum StreamingStrategy {
  Callback{ token: StreamingToken, callback: StreamingCallback },
}
#[derive(CandidType, Deserialize)]
pub struct HttpResponse {
  pub body: serde_bytes::ByteBuf,
  pub headers: Vec<HeaderField>,
  pub streaming_strategy: Option<StreamingStrategy>,
  pub status_code: u16,
}

pub struct Service(pub Principal);
impl Service {
  pub async fn http_streaming_callback(&self, token: &StreamingToken) -> Result<(StreamingCallbackHttpResponse,)> {
    ic_cdk::call(self.0, "httpStreamingCallback", (token,)).await
  }
  pub async fn http_request(&self, request: &HttpRequest) -> Result<(HttpResponse,)> {
    ic_cdk::call(self.0, "http_request", (request,)).await
  }
  pub async fn upload(&self, path: &String, mimeType: &String, chunk: &serde_bytes::ByteBuf, complete: &bool) -> Result<()> {
    ic_cdk::call(self.0, "upload", (path,mimeType,chunk,complete,)).await
  }
}
/// Canister ID: `aaaaa-aa`
pub const CANISTER_ID : Principal = Principal::from_slice(&[]);
pub const service : Service = Service(CANISTER_ID);

