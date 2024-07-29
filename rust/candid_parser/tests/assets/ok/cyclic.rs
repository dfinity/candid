// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
#![allow(dead_code, unused_imports)]
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::api::call::CallResult as Result;

pub type C = Box<A>;
pub type B = Option<C>;
#[derive(CandidType, Deserialize)]
pub struct A(pub Option<B>);
pub type Z = Box<A>;
pub type Y = Z;
pub type X = Y;

pub struct Service(pub Principal);
impl Service {
  pub async fn f(&self, arg0: &A, arg1: &B, arg2: &C, arg3: &X, arg4: &Y, arg5: &Z) -> Result<()> {
    ic_cdk::call(self.0, "f", (arg0,arg1,arg2,arg3,arg4,arg5,)).await
  }
}
pub const CANISTER_ID : Principal = Principal::from_slice(&[]); // aaaaa-aa
pub const service : Service = Service(CANISTER_ID);

