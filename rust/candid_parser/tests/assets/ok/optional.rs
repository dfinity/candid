// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
#![allow(dead_code, unused_imports)]
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::api::call::CallResult as Result;

pub type Option1 = Option<candid::Nat>;
pub type Option2 = Option<Option1>;

pub struct Service(pub Principal);
impl Service {
  pub async fn f(&self) -> Result<(Option1,Option2,)> {
    ic_cdk::call(self.0, "f", ()).await
  }
}
/// Canister ID: `aaaaa-aa`
pub const CANISTER_ID : Principal = Principal::from_slice(&[]);
pub const service : Service = Service(CANISTER_ID);

