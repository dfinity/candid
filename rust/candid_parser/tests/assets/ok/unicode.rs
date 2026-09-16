// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
#![allow(dead_code, unused_imports)]
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::api::call::CallResult as Result;

#[derive(CandidType, Deserialize)]
pub struct A {
  #[serde(rename="\u{e000}")]
  pub _11864174_: candid::Nat,
  #[serde(rename="📦🍦")]
  pub _1832283146_: candid::Nat,
  #[serde(rename="字段名")]
  pub _2119362116_: candid::Nat,
  #[serde(rename="字 段 名2")]
  pub _3133479156_: candid::Nat,
}
#[derive(CandidType, Deserialize)]
pub enum B {
  #[serde(rename="")]
  _0_,
  #[serde(rename="空的")]
  _650764729_,
  #[serde(rename="  空的  ")]
  _1036827129_,
  #[serde(rename="1⃣\u{fe0f}2⃣\u{fe0f}3⃣\u{fe0f}")]
  _3099250646_,
}

pub struct Service(pub Principal);
impl Service {
  pub async fn _0_(&self, arg0: &candid::Nat) -> Result<(candid::Nat,)> {
    ic_cdk::call(self.0, "", (arg0,)).await
  }
  pub async fn _356566390_(&self) -> Result<()> {
    ic_cdk::call(self.0, "✈\u{fe0f}  🚗 ⛱\u{fe0f} ", ()).await
  }
  pub async fn _3300066460_(&self, arg0: &A) -> Result<(B,)> {
    ic_cdk::call(self.0, "函数名", (arg0,)).await
  }
  pub async fn _2669435454_(&self, arg0: &candid::Nat) -> Result<(candid::Nat,)> {
    ic_cdk::call(self.0, "👀", (arg0,)).await
  }
}
/// Canister ID: `aaaaa-aa`
pub const CANISTER_ID : Principal = Principal::from_slice(&[]);
pub const service : Service = Service(CANISTER_ID);

