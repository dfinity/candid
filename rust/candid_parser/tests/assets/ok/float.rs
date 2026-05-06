// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
#![allow(dead_code, unused_imports)]
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::api::call::CallResult as Result;

pub struct Service(pub Principal);
impl Service {
  pub async fn identity32(&self, arg0: &f32) -> Result<(f32,)> {
    ic_cdk::call(self.0, "identity32", (arg0,)).await
  }
  pub async fn to_f32(&self, arg0: &f64) -> Result<(f32,)> {
    ic_cdk::call(self.0, "to_f32", (arg0,)).await
  }
  pub async fn to_f64(&self, arg0: &f32) -> Result<(f64,)> {
    ic_cdk::call(self.0, "to_f64", (arg0,)).await
  }
}
/// Canister ID: `aaaaa-aa`
pub const CANISTER_ID : Principal = Principal::from_slice(&[]);
pub const service : Service = Service(CANISTER_ID);

