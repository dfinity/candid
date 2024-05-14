// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
#![allow(dead_code, unused_imports)]
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::api::call::CallResult as Result;

candid::define_service!(pub S : { "next" : candid::func!(() -> (S)) });

pub struct Service(pub Principal);
impl Service {
  pub async fn next(&self) -> Result<(S,)> {
    ic_cdk::call(self.0, "next", ()).await
  }
}
pub const CANISTER_ID : Principal = Principal::from_slice(&[]); // aaaaa-aa
pub const service : Service = Service(CANISTER_ID);

