// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.

type A = B
type B = Option<A>
type List = Option<List_inner>
#[derive(CandidType, Deserialize)]
struct List_inner { head: candid::Int, tail: List }
#[derive(CandidType, Deserialize)]
enum a { a, b(b) }
#[derive(CandidType, Deserialize)]
struct b (candid::Int,candid::Nat,)
type broker = candid::Service
type f = candid::Func
#[derive(CandidType, Deserialize)]
enum h_arg1 { A(candid::Nat), B(Option<String>) }
#[derive(CandidType, Deserialize)]
struct h_ret0 { _42_: h_ret0_42, id: candid::Nat }
#[derive(CandidType, Deserialize)]
struct h_ret0_42 {}
type list = Option<node>
type my_type = candid::Principal
#[derive(CandidType, Deserialize)]
struct nested {
  _0_: candid::Nat,
  _1_: candid::Nat,
  _2_: (candid::Nat,candid::Int,),
  _3_: nested_3,
  _40_: candid::Nat,
  _41_: nested_41,
  _42_: candid::Nat,
}
#[derive(CandidType, Deserialize)]
struct nested_3 { _0_: candid::Nat, _42_: candid::Nat, _43_: u8 }
#[derive(CandidType, Deserialize)]
enum nested_41 { _42_, A, B, C }
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

