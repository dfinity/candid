// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
#![allow(dead_code, unused_imports)]
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::call::{Call, CallResult as Result};

#[derive(CandidType, Deserialize)]
pub struct O(pub Option<Box<O>>);
#[derive(CandidType, Deserialize)]
pub struct FieldArg { pub test: u16, pub _1291438163_: u8 }
#[derive(CandidType, Deserialize)]
pub struct FieldRet {}
#[derive(CandidType, Deserialize)]
pub struct FieldnatArg {
  pub _2_: candid::Int,
  #[serde(rename="2")]
  pub _50_: candid::Nat,
}
#[derive(CandidType, Deserialize)]
pub struct Node { pub head: candid::Nat, pub tail: Box<List> }
#[derive(CandidType, Deserialize)]
pub struct List(pub Option<Node>);
#[derive(CandidType, Deserialize)]
pub enum If {
  #[serde(rename="branch")]
  Branch{ val: candid::Int, left: Box<If>, right: Box<If> },
  #[serde(rename="leaf")]
  Leaf(candid::Int),
}
candid::define_function!(pub StreamInnerNext : () -> (Stream) query);
#[derive(CandidType, Deserialize)]
pub struct StreamInner { pub head: candid::Nat, pub next: StreamInnerNext }
#[derive(CandidType, Deserialize)]
pub struct Stream(pub Option<StreamInner>);
candid::define_service!(pub Return : {
  "f" : T::ty();
  "g" : candid::func!((List) -> (If, Stream));
});
candid::define_function!(pub T : (Return) -> ());
#[derive(CandidType, Deserialize)]
pub enum VariantArg { A, B, C, D(f64) }

pub struct Service(pub Principal);
impl Service {
  pub async fn oneway(&self) -> Result<()> {
    Ok(Call::bounded_wait(self.0, "Oneway").await?.candid()?)
  }
  pub async fn f(&self, arg0: &O) -> Result<(O,)> {
    Ok(Call::bounded_wait(self.0, "f_").with_arg(arg0).await?.candid()?)
  }
  pub async fn field(&self, arg0: &FieldArg) -> Result<(FieldRet,)> {
    Ok(Call::bounded_wait(self.0, "field").with_arg(arg0).await?.candid()?)
  }
  pub async fn fieldnat(&self, arg0: &FieldnatArg) -> Result<((candid::Int),)> {
    Ok(Call::bounded_wait(self.0, "fieldnat").with_arg(arg0).await?.candid()?)
  }
  pub async fn oneway(&self, arg0: &u8) -> Result<()> {
    Ok(Call::bounded_wait(self.0, "oneway").with_arg(arg0).await?.candid()?)
  }
  pub async fn oneway(&self, arg0: &u8) -> Result<()> {
    Ok(Call::bounded_wait(self.0, "oneway_").with_arg(arg0).await?.candid()?)
  }
  pub async fn query(&self, arg0: &serde_bytes::ByteBuf) -> Result<(serde_bytes::ByteBuf,)> {
    Ok(Call::bounded_wait(self.0, "query").with_arg(arg0).await?.candid()?)
  }
  pub async fn r#return(&self, arg0: &O) -> Result<(O,)> {
    Ok(Call::bounded_wait(self.0, "return").with_arg(arg0).await?.candid()?)
  }
  pub async fn service(&self, server: &Return) -> Result<()> {
    Ok(Call::bounded_wait(self.0, "service").with_arg(server).await?.candid()?)
  }
  pub async fn tuple(&self, arg0: &(candid::Int, serde_bytes::ByteBuf, String)) -> Result<((candid::Int, u8),)> {
    Ok(Call::bounded_wait(self.0, "tuple").with_arg(arg0).await?.candid()?)
  }
  pub async fn variant(&self, arg0: &VariantArg) -> Result<()> {
    Ok(Call::bounded_wait(self.0, "variant").with_arg(arg0).await?.candid()?)
  }
}
/// Canister ID: `aaaaa-aa`
pub const CANISTER_ID : Principal = Principal::from_slice(&[]);
pub const service : Service = Service(CANISTER_ID);

