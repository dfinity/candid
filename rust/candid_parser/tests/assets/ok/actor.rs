// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
#![allow(dead_code, unused_imports)]
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::api::call::CallResult as Result;

pub type DoubleNestedOpt = Option<Option<Option<String>>>;
candid::define_function!(pub F : (i8) -> (i8));
candid::define_function!(pub H : (F) -> (F));
pub type G = F;
pub type NestedOpt = Option<Option<String>>;
pub type NormalOpt = Option<String>;
#[derive(CandidType, Deserialize)]
pub struct RecursiveOpt(pub Option<Box<RecursiveOpt>>);

pub struct Service(pub Principal);
impl Service {
  pub async fn double_nested_opt(&self, arg0: &DoubleNestedOpt) -> Result<(DoubleNestedOpt,)> {
    ic_cdk::call(self.0, "doubleNestedOpt", (arg0,)).await
  }
  pub async fn f(&self, arg0: &candid::Nat) -> Result<(H,)> {
    ic_cdk::call(self.0, "f", (arg0,)).await
  }
  pub async fn g(&self, arg0: &i8) -> Result<(i8,)> {
    ic_cdk::call(self.0, "g", (arg0,)).await
  }
  pub async fn h(&self, arg0: &i8) -> Result<(i8,)> {
    ic_cdk::call(self.0, "h", (arg0,)).await
  }
  pub async fn nested_opt(&self, arg0: &NestedOpt) -> Result<(NestedOpt,)> {
    ic_cdk::call(self.0, "nestedOpt", (arg0,)).await
  }
  pub async fn normal_opt(&self, arg0: &NormalOpt) -> Result<(NormalOpt,)> {
    ic_cdk::call(self.0, "normalOpt", (arg0,)).await
  }
  pub async fn recursive_opt(&self, arg0: &RecursiveOpt) -> Result<(RecursiveOpt,)> {
    ic_cdk::call(self.0, "recursiveOpt", (arg0,)).await
  }
}
pub const CANISTER_ID : Principal = Principal::from_slice(&[]); // aaaaa-aa
pub const service : Service = Service(CANISTER_ID);

