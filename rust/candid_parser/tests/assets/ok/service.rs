// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
#![allow(dead_code, unused_imports)]
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::call::{Call, CallResult as Result};

candid::define_function!(pub Func : () -> (Service));
candid::define_service!(pub Service : { "f" : Func::ty() });
pub type Service2 = Box<Service>;
#[derive(CandidType, Deserialize)]
pub enum AsVariantRet {
  #[serde(rename="a")]
  A(Service2),
  #[serde(rename="b")]
  B{ f: Option<Func> },
}

pub struct Service(pub Principal);
impl Service {
  pub async fn as_array(&self) -> Result<(Vec<Service2>,Vec<Func>,)> {
    Ok(Call::bounded_wait(self.0, "asArray").await?.candid()?)
  }
  pub async fn as_principal(&self) -> Result<(Service2,Func,)> {
    Ok(Call::bounded_wait(self.0, "asPrincipal").await?.candid()?)
  }
  pub async fn as_record(&self) -> Result<((Service2, Option<Service>, Func),)> {
    Ok(Call::bounded_wait(self.0, "asRecord").await?.candid()?)
  }
  pub async fn as_variant(&self) -> Result<(AsVariantRet,)> {
    Ok(Call::bounded_wait(self.0, "asVariant").await?.candid()?)
  }
}
/// Canister ID: `aaaaa-aa`
pub const CANISTER_ID : Principal = Principal::from_slice(&[]);
pub const service : Service = Service(CANISTER_ID);

