// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
#![allow(dead_code, unused_imports)]
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::api::call::CallResult as Result;

#[derive(CandidType, Deserialize)]
pub struct T {
  #[serde(rename="\"")]
  pub _34_: candid::Nat,
  #[serde(rename="\'")]
  pub _39_: candid::Nat,
  #[serde(rename="\"\'")]
  pub _7621_: candid::Nat,
  #[serde(rename="\\\n\'\"")]
  pub _1020746185_: candid::Nat,
}

pub struct Service(pub Principal);
impl Service {
  pub async fn _2635468193_(&self, arg0: &T) -> Result<()> {
    ic_cdk::call(self.0, "\n\'\"\'\'\"\"\r\t", (arg0,)).await
  }
}
pub const CANISTER_ID : Principal = Principal::from_slice(&[]); // aaaaa-aa
pub const service : Service = Service(CANISTER_ID);

