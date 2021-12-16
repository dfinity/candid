// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.

type A = B
type B = Option<A>
type list = Option<node>
#[derive(CandidType, Deserialize)]
struct node { head: candid::Nat, tail: list }

type s = candid::Service
type stream = Option<stream_inner>
#[derive(CandidType, Deserialize)]
struct stream_inner { head: candid::Nat, next: candid::Func }

type t = candid::Func
#[derive(CandidType, Deserialize)]
enum tree {
  branch{ val: candid::Int, left: tree, right: tree },
  leaf(candid::Int),
}

pub trait SERVICE {
  pub fn f(arg0: s) -> ();
  pub fn g(arg0: list) -> (B, tree, stream);
}
