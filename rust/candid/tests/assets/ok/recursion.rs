// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.

type A = Box<B>;
#[derive(CandidType, Deserialize)]
struct B(Option<A>);

type list = Option<Box<node>>;
#[derive(CandidType, Deserialize)]
struct node { head: candid::Nat, tail: list }

type s = candid::Service;
#[derive(CandidType, Deserialize)]
struct stream(Option<Box<stream_inner>>);

#[derive(CandidType, Deserialize)]
struct stream_inner { head: candid::Nat, next: candid::Func }

#[derive(CandidType, Deserialize)]
struct t(candid::Func);

#[derive(CandidType, Deserialize)]
enum tree {
  branch{ val: candid::Int, left: Box<tree>, right: Box<tree> },
  leaf(candid::Int),
}

struct SERVICE(candid::Principal);
impl SERVICE{
  pub async fn f(&self, arg0: s) -> () {
    ic_cdk::call(self.0, "f", (arg0,)).await.unwrap()
  }
  pub async fn g(&self, arg0: list) -> (B, tree, stream) {
    ic_cdk::call(self.0, "g", (arg0,)).await.unwrap()
  }
}
