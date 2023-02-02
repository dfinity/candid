// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
use candid::{self, CandidType, Deserialize};
use ic_cdk::api::call::CallResult;

#[derive(CandidType, Deserialize)]
pub struct List(Option<(candid::Int,Box<List>,)>);

pub struct SERVICE(pub candid::Principal);
impl SERVICE{
  pub async fn get(&self) -> CallResult<(List,)> {
    ic_cdk::call(self.0, "get", ()).await
  }
  pub async fn set(&self, arg0: List) -> CallResult<(List,)> {
    ic_cdk::call(self.0, "set", (arg0,)).await
  }
}
