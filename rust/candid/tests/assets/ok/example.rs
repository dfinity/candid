// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::api::call::CallResult as Result;

#[derive(CandidType, Deserialize)]
pub struct node { head: candid::Nat, tail: Box<list> }

#[derive(CandidType, Deserialize)]
pub struct list(Option<node>);

pub type my_type = Principal;
#[derive(CandidType, Deserialize)]
pub struct List_inner { head: candid::Int, tail: Box<List> }

#[derive(CandidType, Deserialize)]
pub struct List(Option<List_inner>);

#[derive(CandidType, Deserialize)]
pub struct nested_3 { _0_: candid::Nat, _42_: candid::Nat, _43_: u8 }

#[derive(CandidType, Deserialize)]
pub enum nested_41 { _42_, A, B, C }

#[derive(CandidType, Deserialize)]
pub struct nested {
  _0_: candid::Nat,
  _1_: candid::Nat,
  _2_: (candid::Nat,candid::Int,),
  _3_: nested_3,
  _40_: candid::Nat,
  _41_: nested_41,
  _42_: candid::Nat,
}

candid::define_service!(pub broker_find_ret0 : {
  "current" : candid::func!(() -> (u32));
  "up" : candid::func!(() -> ());
});
candid::define_service!(pub broker : {
  "find" : candid::func!((String) -> (broker_find_ret0));
});
#[derive(CandidType, Deserialize)]
pub enum h_arg1 { A(candid::Nat), B(Option<String>) }

#[derive(CandidType, Deserialize)]
pub struct h_ret0_42 {}

#[derive(CandidType, Deserialize)]
pub struct h_ret0 { _42_: h_ret0_42, id: candid::Nat }

candid::define_function!(pub f_arg1 : (i32) -> (i64));
candid::define_function!(pub f : (List, f_arg1) -> (Option<List>));
#[derive(CandidType, Deserialize)]
pub struct b (candid::Int,candid::Nat,);

#[derive(CandidType, Deserialize)]
pub enum a { a, b(b) }

pub struct SERVICE(pub Principal);
impl SERVICE {
  pub async fn f(
    &self,
    arg0: list,
    arg1: serde_bytes::ByteBuf,
    arg2: Option<bool>,
  ) -> Result<()> { ic_cdk::call(self.0, "f", (arg0,arg1,arg2,)).await }
  pub async fn g(
    &self,
    arg0: my_type,
    arg1: List,
    arg2: Option<List>,
    arg3: nested,
  ) -> Result<(candid::Int,broker,)> {
    ic_cdk::call(self.0, "g", (arg0,arg1,arg2,arg3,)).await
  }
  pub async fn h(
    &self,
    arg0: Vec<Option<String>>,
    arg1: h_arg1,
    arg2: Option<List>,
  ) -> Result<(h_ret0,)> { ic_cdk::call(self.0, "h", (arg0,arg1,arg2,)).await }
  pub async fn i(&self, arg0: List, arg1: f_arg1) -> Result<(Option<List>,)> {
    ic_cdk::call(self.0, "i", (arg0,arg1,)).await
  }
  pub async fn x(&self, arg0: a, arg1: b) -> Result<(Option<a>,Option<b>,)> {
    ic_cdk::call(self.0, "x", (arg0,arg1,)).await
  }
}
pub const service: SERVICE = SERVICE(Principal::from_slice(&[])); // aaaaa-aa
