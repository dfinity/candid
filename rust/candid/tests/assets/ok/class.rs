// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::api::call::CallResult as Result;

#[derive(CandidType, Deserialize)]
pub struct List(Option<(candid::Int,Box<List>,)>);

pub struct SERVICE(pub Principal);
impl SERVICE {
  pub async fn get(&self) -> Result<(List,)> {
    ic_cdk::call(self.0, "get", ()).await
  }
  pub async fn set(&self, arg0: List) -> Result<(List,)> {
    ic_cdk::call(self.0, "set", (arg0,)).await
  }
}
pub const service: SERVICE = SERVICE(Principal::from_slice(&[])); // aaaaa-aa
