// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
#![allow(dead_code, unused_imports)]
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::call::{Call, CallResult as Result};

#[derive(CandidType, Deserialize)]
pub struct FArg {}
#[derive(CandidType, Deserialize)]
pub enum FRet {}
#[derive(CandidType, Deserialize)]
pub struct T (pub Box<T>);
#[derive(CandidType, Deserialize)]
pub enum GRet { #[serde(rename="a")] A(Box<T>) }
#[derive(CandidType, Deserialize)]
pub enum HRet { #[serde(rename="a")] A(Box<T>), #[serde(rename="b")] B{} }

pub struct Service(pub Principal);
impl Service {
  pub async fn f(&self, arg0: &FArg) -> Result<(FRet,)> {
    Ok(Call::bounded_wait(self.0, "f").with_arg(arg0).await?.candid()?)
  }
  pub async fn g(&self, arg0: &T) -> Result<(GRet,)> {
    Ok(Call::bounded_wait(self.0, "g").with_arg(arg0).await?.candid()?)
  }
  pub async fn h(&self, arg0: &(T, candid::Empty)) -> Result<(HRet,)> {
    Ok(Call::bounded_wait(self.0, "h").with_arg(arg0).await?.candid()?)
  }
}
/// Canister ID: `aaaaa-aa`
pub const CANISTER_ID : Principal = Principal::from_slice(&[]);
pub const service : Service = Service(CANISTER_ID);

