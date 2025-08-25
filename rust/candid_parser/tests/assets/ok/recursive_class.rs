// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
#![allow(dead_code, unused_imports)]
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::call::{Call, CallResult as Result};

candid::define_service!(pub S : { "next" : candid::func!(() -> (S)) });

pub struct Service(pub Principal);
impl Service {
  pub async fn next(&self) -> Result<S> {
    Ok(Call::bounded_wait(self.0, "next").await?.candid()?)
  }
}
/// Canister ID: `aaaaa-aa`
pub const CANISTER_ID : Principal = Principal::from_slice(&[]);
pub const service : Service = Service(CANISTER_ID);

