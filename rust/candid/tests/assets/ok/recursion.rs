// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
use candid::{self, CandidType, Deserialize};
use ic_cdk::api::call::CallResult;

pub type t = candid::Func;
#[derive(CandidType, Deserialize)]
pub struct node { head: candid::Nat, tail: Box<list> }

#[derive(CandidType, Deserialize)]
pub struct list(Option<node>);

pub type A = Box<B>;
#[derive(CandidType, Deserialize)]
pub struct B(Option<A>);

#[derive(CandidType, Deserialize)]
pub enum tree {
  branch{ val: candid::Int, left: Box<tree>, right: Box<tree> },
  leaf(candid::Int),
}

#[derive(CandidType, Deserialize)]
pub struct stream_inner { head: candid::Nat, next: candid::Func }

#[derive(CandidType, Deserialize)]
pub struct stream(Option<stream_inner>);

#[derive(CandidType, Deserialize)]
pub struct s(candid::Service);

pub struct SERVICE(candid::Principal);
impl SERVICE{
  pub async fn f(&self, arg0: s) -> CallResult<()> {
    ic_cdk::call(self.0, "f", (arg0,)).await
  }
  pub async fn g(&self, arg0: list) -> CallResult<(B,tree,stream,)> {
    ic_cdk::call(self.0, "g", (arg0,)).await
  }
}
