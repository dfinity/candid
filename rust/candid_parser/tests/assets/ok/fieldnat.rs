// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
#![allow(dead_code, unused_imports)]
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::call::{Call, CallResult as Result};

#[derive(CandidType, Deserialize)]
pub struct BarArg { #[serde(rename="2")] pub _50_: candid::Int }
#[derive(CandidType, Deserialize)]
pub enum BarRet { #[serde(rename="e20")] E20, #[serde(rename="e30")] E30 }
#[derive(CandidType, Deserialize)]
pub struct BazArg {
  pub _2_: candid::Int,
  #[serde(rename="2")]
  pub _50_: candid::Nat,
}
#[derive(CandidType, Deserialize)]
pub struct BazRet {}
#[derive(CandidType, Deserialize)]
pub struct Tuple (pub String, pub String);
#[derive(CandidType, Deserialize)]
pub struct NonTuple { pub _1_: String, pub _2_: String }
#[derive(CandidType, Deserialize)]
pub enum BibRet { _0_(candid::Int) }
#[derive(CandidType, Deserialize)]
pub struct FooArg { pub _2_: candid::Int }
#[derive(CandidType, Deserialize)]
pub struct FooRet { pub _2_: candid::Int, pub _2: candid::Int }

pub struct Service(pub Principal);
impl Service {
  pub async fn bab(&self, two: &candid::Int, arg1: &candid::Nat) -> Result<()> {
    Ok(Call::bounded_wait(self.0, "bab").with_args(&(two,arg1,)).await?.candid()?)
  }
  pub async fn bar(&self, arg0: &BarArg) -> Result<(BarRet,)> {
    Ok(Call::bounded_wait(self.0, "bar").with_args(&(arg0,)).await?.candid()?)
  }
  pub async fn bas(&self, arg0: &(candid::Int, candid::Int)) -> Result<((String, candid::Nat),)> {
    Ok(Call::bounded_wait(self.0, "bas").with_args(&(arg0,)).await?.candid()?)
  }
  pub async fn baz(&self, arg0: &BazArg) -> Result<(BazRet,)> {
    Ok(Call::bounded_wait(self.0, "baz").with_args(&(arg0,)).await?.candid()?)
  }
  pub async fn bba(&self, arg0: &Tuple) -> Result<(NonTuple,)> {
    Ok(Call::bounded_wait(self.0, "bba").with_args(&(arg0,)).await?.candid()?)
  }
  pub async fn bib(&self, arg0: &(candid::Int)) -> Result<(BibRet,)> {
    Ok(Call::bounded_wait(self.0, "bib").with_args(&(arg0,)).await?.candid()?)
  }
  pub async fn foo(&self, arg0: &FooArg) -> Result<(FooRet,)> {
    Ok(Call::bounded_wait(self.0, "foo").with_args(&(arg0,)).await?.candid()?)
  }
}
/// Canister ID: `aaaaa-aa`
pub const CANISTER_ID : Principal = Principal::from_slice(&[]);
pub const service : Service = Service(CANISTER_ID);

