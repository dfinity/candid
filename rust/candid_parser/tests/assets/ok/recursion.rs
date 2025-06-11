// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
#![allow(dead_code, unused_imports)]
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::api::call::CallResult as Result;

candid::define_function!(pub T : (S) -> ());
#[derive(CandidType, Deserialize)]
pub struct Node { pub head: candid::Nat, pub tail: Box<List> }
#[derive(CandidType, Deserialize)]
pub struct List(pub Option<Node>);
pub type A = Box<B>;
#[derive(CandidType, Deserialize)]
pub struct B(pub Option<A>);
#[derive(CandidType, Deserialize)]
pub enum Tree {
  #[serde(rename="branch")]
  Branch{ val: candid::Int, left: Box<Tree>, right: Box<Tree> },
  #[serde(rename="leaf")]
  Leaf(candid::Int),
}
candid::define_function!(pub StreamInnerNext : () -> (Stream) query);
#[derive(CandidType, Deserialize)]
pub struct StreamInner { pub head: candid::Nat, pub next: StreamInnerNext }
#[derive(CandidType, Deserialize)]
pub struct Stream(pub Option<StreamInner>);
candid::define_service!(pub S : {
  "f" : T::ty();
  "g" : candid::func!((List) -> (B, Tree, Stream));
});

pub struct Service(pub Principal);
impl Service {
  pub async fn f(&self, server: &S) -> Result<()> {
    ic_cdk::call(self.0, "f", (server,)).await
  }
  pub async fn g(&self, arg0: &List) -> Result<(B,Tree,Stream,)> {
    ic_cdk::call(self.0, "g", (arg0,)).await
  }
}
pub const CANISTER_ID : Principal = Principal::from_slice(&[]); // aaaaa-aa
pub const service : Service = Service(CANISTER_ID);

