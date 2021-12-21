// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
use ic_cdk::export::candid::{self, CandidType, Deserialize};
use ic_cdk::api::call::CallResult;

#[derive(CandidType, Deserialize)]
struct node { head: candid::Nat, tail: Box<list> }

#[derive(CandidType, Deserialize)]
struct list(Option<node>);

type my_type = candid::Principal;
#[derive(CandidType, Deserialize)]
struct List_inner { head: candid::Int, tail: Box<List> }

#[derive(CandidType, Deserialize)]
struct List(Option<List_inner>);

#[derive(CandidType, Deserialize)]
struct nested_3 { _0_: candid::Nat, _42_: candid::Nat, _43_: u8 }

#[derive(CandidType, Deserialize)]
enum nested_41 { _42_, A, B, C }

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

type broker = candid::Service;
#[derive(CandidType, Deserialize)]
enum h_arg1 { A(candid::Nat), B(Option<String>) }

#[derive(CandidType, Deserialize)]
struct h_ret0_42 {}

#[derive(CandidType, Deserialize)]
struct h_ret0 { _42_: h_ret0_42, id: candid::Nat }

type f = candid::Func;
#[derive(CandidType, Deserialize)]
struct b (candid::Int,candid::Nat,)

#[derive(CandidType, Deserialize)]
enum a { a, b(b) }

struct SERVICE(candid::Principal);
impl SERVICE{
  pub async fn f(
    &self,
    arg0: list,
    arg1: Vec<u8>,
    arg2: Option<bool>,
  ) -> CallResult<()> { ic_cdk::call(self.0, "f", (arg0,arg1,arg2,)).await }
  pub async fn g(
    &self,
    arg0: my_type,
    arg1: List,
    arg2: Option<List>,
    arg3: nested,
  ) -> CallResult<(candid::Int,broker,)> {
    ic_cdk::call(self.0, "g", (arg0,arg1,arg2,arg3,)).await
  }
  pub async fn h(
    &self,
    arg0: Vec<Option<String>>,
    arg1: h_arg1,
    arg2: Option<List>,
  ) -> CallResult<(h_ret0,)> {
    ic_cdk::call(self.0, "h", (arg0,arg1,arg2,)).await
  }
  pub async fn i(&self, arg0: List, arg1: candid::Func) -> CallResult<
    (Option<List>,)
  > { ic_cdk::call(self.0, "i", (arg0,arg1,)).await }
  pub async fn x(&self, arg0: a, arg1: b) -> CallResult<
    (Option<a>,Option<b>,)
  > { ic_cdk::call(self.0, "x", (arg0,arg1,)).await }
}
