// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
use ic_cdk::export::candid::{self, CandidType, Deserialize};
use ic_cdk::api::call::CallResult;

#[derive(CandidType, Deserialize)]
struct List(Option<(candid::Int,Box<List>,)>);

struct SERVICE(candid::Principal);
impl SERVICE{
  pub async fn get(&self) -> CallResult<(List,)> {
    ic_cdk::call(self.0, "get", ()).await
  }
  pub async fn set(&self, arg0: List) -> CallResult<(List,)> {
    ic_cdk::call(self.0, "set", (arg0,)).await
  }
}
