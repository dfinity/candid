// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
#![allow(dead_code, unused_imports)]
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::api::call::CallResult as Result;

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
    ic_cdk::call(self.0, "asArray", ()).await
  }
  pub async fn as_principal(&self) -> Result<(Service2,Func,)> {
    ic_cdk::call(self.0, "asPrincipal", ()).await
  }
  pub async fn as_record(&self) -> Result<((Service2,Option<Service>,Func,),)> {
    ic_cdk::call(self.0, "asRecord", ()).await
  }
  pub async fn as_variant(&self) -> Result<(AsVariantRet,)> {
    ic_cdk::call(self.0, "asVariant", ()).await
  }
}
pub const CANISTER_ID : Principal = Principal::from_slice(&[]); // aaaaa-aa
pub const service : Service = Service(CANISTER_ID);

