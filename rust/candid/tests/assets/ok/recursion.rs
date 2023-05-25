// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::api::call::CallResult as Result;

candid::define_function!(pub t : (s) -> ());
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

candid::define_function!(pub stream_inner_next : () -> (stream) query);
#[derive(CandidType, Deserialize)]
pub struct stream_inner { head: candid::Nat, next: stream_inner_next }

#[derive(CandidType, Deserialize)]
pub struct stream(Option<stream_inner>);

candid::define_service!(pub s : {
  "f" : t::ty();
  "g" : candid::func!((list) -> (B, tree, stream));
});
pub struct SERVICE(pub Principal);
impl SERVICE {
  pub async fn f(&self, arg0: s) -> Result<()> {
    ic_cdk::call(self.0, "f", (arg0,)).await
  }
  pub async fn g(&self, arg0: list) -> Result<(B,tree,stream,)> {
    ic_cdk::call(self.0, "g", (arg0,)).await
  }
}
pub const service: SERVICE = SERVICE(Principal::from_slice(&[])); // aaaaa-aa
