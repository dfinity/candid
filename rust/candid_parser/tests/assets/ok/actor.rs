// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
#![allow(dead_code, unused_imports)]
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::call::{Call, CallResult as Result};

candid::define_function!(pub F : (i8) -> (i8));
candid::define_function!(pub H : (F) -> (F));
pub type G = F;
#[derive(CandidType, Deserialize)]
pub struct O(pub Option<Box<O>>);

pub struct Service(pub Principal);
impl Service {
  pub async fn f(&self, arg0: &candid::Nat) -> Result<H> {
    Ok(Call::bounded_wait(self.0, "f").with_arg(arg0).await?.candid()?)
  }
  pub async fn g(&self, arg0: &i8) -> Result<i8> {
    Ok(Call::bounded_wait(self.0, "g").with_arg(arg0).await?.candid()?)
  }
  pub async fn h(&self, arg0: &i8) -> Result<i8> {
    Ok(Call::bounded_wait(self.0, "h").with_arg(arg0).await?.candid()?)
  }
  pub async fn h_2(&self, arg0: &F) -> Result<F> {
    Ok(Call::bounded_wait(self.0, "h2").with_arg(arg0).await?.candid()?)
  }
  pub async fn o(&self, arg0: &O) -> Result<O> {
    Ok(Call::bounded_wait(self.0, "o").with_arg(arg0).await?.candid()?)
  }
}
/// Canister ID: `aaaaa-aa`
pub const CANISTER_ID : Principal = Principal::from_slice(&[]);
pub const service : Service = Service(CANISTER_ID);

