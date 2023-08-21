// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::api::call::CallResult as Result;

#[derive(CandidType, Deserialize)]
pub struct Node { head: candid::Nat, tail: Box<List> }

#[derive(CandidType, Deserialize)]
pub struct List(Option<Node>);

pub type MyType = Principal;
#[derive(CandidType, Deserialize)]
pub struct ListInner { head: candid::Int, tail: Box<List> }

#[derive(CandidType, Deserialize)]
pub struct List(Option<ListInner>);

#[derive(CandidType, Deserialize)]
pub struct Nested3 { _0_: candid::Nat, _42_: candid::Nat, _43_: u8 }

#[derive(CandidType, Deserialize)]
pub enum Nested41 { _42_, A, B, C }

#[derive(CandidType, Deserialize)]
pub struct Nested {
  _0_: candid::Nat,
  _1_: candid::Nat,
  _2_: (candid::Nat,candid::Int,),
  _3_: Nested3,
  _40_: candid::Nat,
  _41_: Nested41,
  _42_: candid::Nat,
}

candid::define_service!(pub BrokerFindRet : {
  "current" : candid::func!(() -> (u32));
  "up" : candid::func!(() -> ());
});
candid::define_service!(pub Broker : {
  "find" : candid::func!((String) -> (BrokerFindRet));
});
#[derive(CandidType, Deserialize)]
pub enum HArg1 { A(candid::Nat), B(Option<String>) }

#[derive(CandidType, Deserialize)]
pub struct HRet42 {}

#[derive(CandidType, Deserialize)]
pub struct HRet { _42_: HRet42, id: candid::Nat }

candid::define_function!(pub FArg1 : (i32) -> (i64));
candid::define_function!(pub F : (List, FArg1) -> (Option<List>));
#[derive(CandidType, Deserialize)]
pub struct B (candid::Int,candid::Nat,);

#[derive(CandidType, Deserialize)]
pub enum A { #[serde(rename="a")] A, #[serde(rename="b")] B(B) }

pub struct SERVICE(pub Principal);
impl SERVICE {
  pub async fn f(
    &self,
    arg0: List,
    arg1: serde_bytes::ByteBuf,
    arg2: Option<bool>,
  ) -> Result<()> { ic_cdk::call(self.0, "f", (arg0,arg1,arg2,)).await }
  pub async fn g(
    &self,
    arg0: MyType,
    arg1: List,
    arg2: Option<List>,
    arg3: Nested,
  ) -> Result<(candid::Int,Broker,)> {
    ic_cdk::call(self.0, "g", (arg0,arg1,arg2,arg3,)).await
  }
  pub async fn h(
    &self,
    arg0: Vec<Option<String>>,
    arg1: HArg1,
    arg2: Option<List>,
  ) -> Result<(HRet,)> { ic_cdk::call(self.0, "h", (arg0,arg1,arg2,)).await }
  pub async fn i(&self, arg0: List, arg1: FArg1) -> Result<(Option<List>,)> {
    ic_cdk::call(self.0, "i", (arg0,arg1,)).await
  }
  pub async fn x(&self, arg0: A, arg1: B) -> Result<(Option<A>,Option<B>,)> {
    ic_cdk::call(self.0, "x", (arg0,arg1,)).await
  }
}
pub const service: SERVICE = SERVICE(Principal::from_slice(&[])); // aaaaa-aa
