// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
use ic_cdk::export::candid::{self, CandidType, Deserialize};
use ic_cdk::api::call::CallResult;

type t = candid::Func;
#[derive(CandidType, Deserialize)]
struct node { head: candid::Nat, tail: Box<list> }

#[derive(CandidType, Deserialize)]
struct list(Option<node>);

type A = Box<B>;
#[derive(CandidType, Deserialize)]
struct B(Option<A>);

#[derive(CandidType, Deserialize)]
enum tree {
  branch{ val: candid::Int, left: Box<tree>, right: Box<tree> },
  leaf(candid::Int),
}

#[derive(CandidType, Deserialize)]
struct stream_inner { head: candid::Nat, next: candid::Func }

#[derive(CandidType, Deserialize)]
struct stream(Option<stream_inner>);

#[derive(CandidType, Deserialize)]
struct s(candid::Service);

struct SERVICE(candid::Principal);
impl SERVICE{
  pub async fn f(&self, arg0: s) -> CallResult<()> {
    ic_cdk::call(self.0, "f", (arg0,)).await
  }
  pub async fn g(&self, arg0: list) -> CallResult<(B,tree,stream,)> {
    ic_cdk::call(self.0, "g", (arg0,)).await
  }
}
