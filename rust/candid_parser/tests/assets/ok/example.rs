// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
#![allow(dead_code, unused_imports)]
use candid::{self, CandidType, Deserialize, Principal, Encode, Decode};
use ic_cdk::api::call::CallResult as Result;

#[derive(CandidType, Deserialize)]
pub struct B (pub candid::Int,pub candid::Nat,);
#[derive(CandidType, Deserialize)]
pub struct Node { pub head: candid::Nat, pub tail: Box<List> }
#[derive(CandidType, Deserialize)]
pub struct List(Option<Node>);
pub type A = Box<B>;
#[derive(CandidType, Deserialize)]
pub struct B(Option<A>);
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
pub struct Stream(Option<StreamInner>);
candid::define_service!(pub S : {
  "f" : T::ty();
  "g" : candid::func!((List) -> (B, Tree, Stream));
});
candid::define_function!(pub T : (S) -> ());
pub type MyType = Principal;
#[derive(CandidType, Deserialize)]
pub struct ListInner { pub head: candid::Int, pub tail: Box<List> }
#[derive(CandidType, Deserialize)]
pub struct List(Option<ListInner>);
#[derive(CandidType, Deserialize)]
pub struct Nested3 { pub _0_: candid::Nat, pub _42_: candid::Nat, pub _43_: u8 }
#[derive(CandidType, Deserialize)]
pub enum Nested41 { _42_, A, B, C }
#[derive(CandidType, Deserialize)]
pub struct Nested {
  pub _0_: candid::Nat,
  pub _1_: candid::Nat,
  pub _2_: (candid::Nat,candid::Int,),
  pub _3_: Nested3,
  pub _40_: candid::Nat,
  pub _41_: Nested41,
  pub _42_: candid::Nat,
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
pub struct HRet { pub _42_: HRet42, pub id: candid::Nat }
candid::define_function!(pub FArg1 : (i32) -> (i64));
candid::define_function!(pub F : (List, FArg1) -> (Option<List>));
#[derive(CandidType, Deserialize)]
pub enum A { #[serde(rename="a")] A, #[serde(rename="b")] B(B) }

pub struct Service(pub Principal);
impl Service {
  pub async fn bbbbb(&self, arg0: B) -> Result<()> {
    ic_cdk::call(self.0, "bbbbb", (arg0,)).await
  }
  pub async fn f(&self, arg0: S) -> Result<()> {
    ic_cdk::call(self.0, "f", (arg0,)).await
  }
  pub async fn f_1(&self, arg0: List, arg1: serde_bytes::ByteBuf, arg2: Option<bool>) -> Result<()> {
    ic_cdk::call(self.0, "f1", (arg0,arg1,arg2,)).await
  }
  pub async fn g(&self, arg0: List) -> Result<(B,Tree,Stream,)> {
    ic_cdk::call(self.0, "g", (arg0,)).await
  }
  pub async fn g_1(&self, arg0: MyType, arg1: List, arg2: Option<List>, arg3: Nested) -> Result<(candid::Int,Broker,)> {
    ic_cdk::call(self.0, "g1", (arg0,arg1,arg2,arg3,)).await
  }
  pub async fn h(&self, arg0: Vec<Option<String>>, arg1: HArg1, arg2: Option<List>) -> Result<(HRet,)> {
    ic_cdk::call(self.0, "h", (arg0,arg1,arg2,)).await
  }
  pub async fn i(&self, arg0: List, arg1: FArg1) -> Result<(Option<List>,)> {
    ic_cdk::call(self.0, "i", (arg0,arg1,)).await
  }
  pub async fn x(&self, arg0: A, arg1: B) -> Result<(Option<A>,Option<B>,)> {
    ic_cdk::call(self.0, "x", (arg0,arg1,)).await
  }
}
pub const CANISTER_ID : Principal = Principal::from_slice(&[]); // aaaaa-aa
pub const service : Service = Service(CANISTER_ID);

