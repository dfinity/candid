// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::api::call::CallResult;

candid::define_function!(pub f : (i8) -> (i8));
candid::define_function!(pub h : (f) -> (f));
pub type g = f;
#[derive(CandidType, Deserialize)]
pub struct o(Option<Box<o>>);

pub struct SERVICE(pub Principal);
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
pub fn service() -> SERVICE {
  SERVICE(Principal::from_text("aaaaa-aa").unwrap())
}
