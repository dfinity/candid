// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
use ic_cdk::export::candid::{self, CandidType, Deserialize};
use ic_cdk::api::call::CallResult;

#[derive(CandidType, Deserialize)]
struct s(candid::Service);

struct SERVICE(candid::Principal);
impl SERVICE{
  pub async fn next(&self) -> CallResult<(s,)> {
    ic_cdk::call(self.0, "next", ()).await
  }
}
