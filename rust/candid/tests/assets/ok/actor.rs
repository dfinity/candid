// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
use ic_cdk::export::candid::{self, CandidType, Deserialize};
use ic_cdk::api::call::CallResult;

type f = candid::Func;
type h = candid::Func;
type g = f;
#[derive(CandidType, Deserialize)]
struct o(Option<Box<o>>);

struct SERVICE(candid::Principal);
impl SERVICE{
  pub async fn f(&self, arg0: candid::Nat) -> CallResult<(h,)> {
    ic_cdk::call(self.0, "f", (arg0,)).await
  }
  pub async fn g(&self, arg0: i8) -> CallResult<(i8,)> {
    ic_cdk::call(self.0, "g", (arg0,)).await
  }
  pub async fn h(&self, arg0: i8) -> CallResult<(i8,)> {
    ic_cdk::call(self.0, "h", (arg0,)).await
  }
  pub async fn o(&self, arg0: o) -> CallResult<(o,)> {
    ic_cdk::call(self.0, "o", (arg0,)).await
  }
}
