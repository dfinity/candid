// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
use ic_cdk::export::candid::{self, CandidType, Deserialize};
use ic_cdk::api::call::CallResult;

#[derive(CandidType, Deserialize)]
struct t {
  #[serde(rename="\"")]
  _34_: candid::Nat,
  #[serde(rename="\'")]
  _39_: candid::Nat,
  #[serde(rename="\"\'")]
  _7621_: candid::Nat,
  #[serde(rename="\\\n\'\"")]
  _1020746185_: candid::Nat,
}

struct SERVICE(candid::Principal);
impl SERVICE{
  pub async fn _2635468193_(&self, arg0: t) -> CallResult<()> {
    ic_cdk::call(self.0, "\n\'\"\'\'\"\"\r\t", (arg0,)).await
  }
}
