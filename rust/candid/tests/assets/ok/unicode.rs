// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::api::call::CallResult as Result;

#[derive(CandidType, Deserialize)]
pub struct A {
  #[serde(rename="\u{e000}")]
  _11864174_: candid::Nat,
  #[serde(rename="📦🍦")]
  _1832283146_: candid::Nat,
  #[serde(rename="字段名")]
  _2119362116_: candid::Nat,
  #[serde(rename="字 段 名2")]
  _3133479156_: candid::Nat,
}

#[derive(CandidType, Deserialize)]
pub enum B {
  #[serde(rename="")]
  _0_,
  #[serde(rename="空的")]
  _650764729_,
  #[serde(rename="  空的  ")]
  _1036827129_,
  #[serde(rename="1⃣️2⃣️3⃣️")]
  _3099250646_,
}

pub struct SERVICE(pub Principal);
impl SERVICE {
  pub async fn _0_(&self, arg0: candid::Nat) -> Result<(candid::Nat,)> {
    ic_cdk::call(self.0, "", (arg0,)).await
  }
  pub async fn _356566390_(&self) -> Result<()> {
    ic_cdk::call(self.0, "✈️  🚗 ⛱️ ", ()).await
  }
  pub async fn _3300066460_(&self, arg0: A) -> Result<(B,)> {
    ic_cdk::call(self.0, "函数名", (arg0,)).await
  }
  pub async fn _2669435454_(&self, arg0: candid::Nat) -> Result<
    (candid::Nat,)
  > { ic_cdk::call(self.0, "👀", (arg0,)).await }
}
pub const service: SERVICE = SERVICE(Principal::from_slice(&[])); // aaaaa-aa
