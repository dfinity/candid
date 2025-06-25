// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
#![allow(dead_code, unused_imports)]
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::api::call::CallResult as Result;

candid::define_function!(pub Fn : (candid::Nat) -> (candid::Nat) query);
candid::define_function!(pub HighOrderFnInlineArg1 : (candid::Nat) -> (
    candid::Nat,
  ) query);
pub type Gn = Fn;
#[derive(CandidType, Deserialize)]
pub struct RNested { pub r#fn: Gn }
#[derive(CandidType, Deserialize)]
pub struct R {
  pub x: candid::Nat,
  pub r#fn: Fn,
  pub gn: Gn,
  pub nested: RNested,
}
candid::define_function!(pub RInlineFn : (candid::Nat) -> (candid::Nat) query);
#[derive(CandidType, Deserialize)]
pub struct RInline { pub x: candid::Nat, pub r#fn: RInlineFn }

pub struct Service(pub Principal);
impl Service {
  pub async fn add_two(&self, arg0: &candid::Nat) -> Result<(candid::Nat,)> {
    ic_cdk::call(self.0, "add_two", (arg0,)).await
  }
  pub async fn r#fn(&self, arg0: &candid::Nat) -> Result<(candid::Nat,)> {
    ic_cdk::call(self.0, "fn", (arg0,)).await
  }
  pub async fn high_order_fn(&self, arg0: &candid::Nat, arg1: &Fn) -> Result<(candid::Nat,)> {
    ic_cdk::call(self.0, "high_order_fn", (arg0,arg1,)).await
  }
  pub async fn high_order_fn_inline(&self, arg0: &candid::Nat, arg1: &HighOrderFnInlineArg1) -> Result<(candid::Nat,)> {
    ic_cdk::call(self.0, "high_order_fn_inline", (arg0,arg1,)).await
  }
  pub async fn high_order_fn_via_id(&self, arg0: &candid::Nat, arg1: &Gn) -> Result<(Fn,)> {
    ic_cdk::call(self.0, "high_order_fn_via_id", (arg0,arg1,)).await
  }
  pub async fn high_order_fn_via_record(&self, arg0: &R) -> Result<(candid::Nat,)> {
    ic_cdk::call(self.0, "high_order_fn_via_record", (arg0,)).await
  }
  pub async fn high_order_fn_via_record_inline(&self, arg0: &RInline) -> Result<(candid::Nat,)> {
    ic_cdk::call(self.0, "high_order_fn_via_record_inline", (arg0,)).await
  }
}
pub const CANISTER_ID : Principal = Principal::from_slice(&[]); // aaaaa-aa
pub const service : Service = Service(CANISTER_ID);

