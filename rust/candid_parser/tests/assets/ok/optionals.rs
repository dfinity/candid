// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
#![allow(dead_code, unused_imports)]
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::api::call::CallResult as Result;

pub type DoubleNestedOpt = Option<Option<Option<String>>>;
pub type NestedOpt = Option<Option<String>>;
pub type NormalOpt = Option<String>;
#[derive(CandidType, Deserialize)]
pub struct RecursiveOpt(pub Option<Box<RecursiveOpt>>);

pub struct Service(pub Principal);
impl Service {
  pub async fn double_nested_opt(&self, arg0: &DoubleNestedOpt) -> Result<(DoubleNestedOpt,)> {
    ic_cdk::call(self.0, "doubleNested_opt", (arg0,)).await
  }
  pub async fn nested_opt(&self, arg0: &NestedOpt) -> Result<(NestedOpt,)> {
    ic_cdk::call(self.0, "nested_opt", (arg0,)).await
  }
  pub async fn normal_opt(&self, arg0: &NormalOpt) -> Result<(NormalOpt,)> {
    ic_cdk::call(self.0, "normal_opt", (arg0,)).await
  }
  pub async fn recursive_opt(&self, arg0: &RecursiveOpt) -> Result<(RecursiveOpt,)> {
    ic_cdk::call(self.0, "recursive_opt", (arg0,)).await
  }
}
pub const CANISTER_ID : Principal = Principal::from_slice(&[]); // aaaaa-aa
pub const service : Service = Service(CANISTER_ID);

