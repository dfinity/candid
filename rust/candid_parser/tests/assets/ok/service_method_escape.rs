// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
#![allow(dead_code, unused_imports)]
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::api::call::CallResult as Result;

candid::define_function!(pub F : () -> ());
candid::define_service!(pub Inner : {
  "backslash\\" : F::ty();
  "braces { } and parens ( )" : F::ty();
  "comment markers // and /* */" : F::ty();
  "newline\nand carriage return\r" : F::ty();
  "quote\"" : F::ty();
  "tab\tand semicolon;" : F::ty();
});

pub struct Service(pub Principal);
impl Service {
  pub async fn ping(&self) -> Result<(String,)> {
    ic_cdk::call(self.0, "ping", ()).await
  }
  pub async fn use_inner(&self, arg0: &Inner) -> Result<()> {
    ic_cdk::call(self.0, "use_inner", (arg0,)).await
  }
}
/// Canister ID: `aaaaa-aa`
pub const CANISTER_ID : Principal = Principal::from_slice(&[]);
pub const service : Service = Service(CANISTER_ID);

