// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
#![allow(dead_code, unused_imports)]
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::api::call::CallResult as Result;

candid::define_function!(pub F : (i8) -> (i8));
candid::define_function!(pub H : (F) -> (F));
pub type G = F;
#[derive(CandidType, Deserialize)]
pub struct O(pub Option<Box<O>>);

pub struct Service(pub Principal);
impl Service {
  pub async fn f(&self, arg0: &candid::Nat) -> Result<(H,)> {
    ic_cdk::call(self.0, "f", (arg0,)).await
  }
  pub async fn g(&self, arg0: &i8) -> Result<(i8,)> {
    ic_cdk::call(self.0, "g", (arg0,)).await
  }
  pub async fn h(&self, arg0: &i8) -> Result<(i8,)> {
    ic_cdk::call(self.0, "h", (arg0,)).await
  }
  pub async fn h_2(&self, arg0: &F) -> Result<(F,)> {
    ic_cdk::call(self.0, "h2", (arg0,)).await
  }
  pub async fn o(&self, arg0: &O) -> Result<(O,)> {
    ic_cdk::call(self.0, "o", (arg0,)).await
  }
}
pub const CANISTER_ID : Principal = Principal::from_slice(&[]); // aaaaa-aa
pub const service : Service = Service(CANISTER_ID);

