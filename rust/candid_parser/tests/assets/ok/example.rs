// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
#![allow(dead_code, unused_imports)]
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::api::call::CallResult as Result;

#[derive(CandidType, Deserialize, Debug)]
pub(crate) struct B (pub(crate) candid::Int,pub(crate) u128,);
#[derive(CandidType, Deserialize, Debug)]
pub(crate) struct Node { pub(crate) head: u128, pub(crate) tail: Box<List> }
#[derive(CandidType, Deserialize, Debug)]
pub(crate) struct List(pub(crate) Option<Node>);
pub(crate) type A = Box<B>;
#[derive(CandidType, Deserialize, Debug)]
pub(crate) struct B(pub(crate) Option<A>);
#[derive(CandidType, Deserialize, Debug)]
pub(crate) enum Tree {
  #[serde(rename="branch")]
  Branch{ val: candid::Int, left: Box<Tree>, right: Box<Tree> },
  #[serde(rename="leaf")]
  Leaf(candid::Int),
}
candid::define_function!(pub(crate) StreamInnerNext : () -> (Stream) query);
#[derive(CandidType, Deserialize, Debug)]
pub(crate) struct StreamInner {
  pub(crate) head: u128,
  pub(crate) next: StreamInnerNext,
}
#[derive(CandidType, Deserialize, Debug)]
pub(crate) struct Stream(pub(crate) Option<StreamInner>);
candid::define_service!(pub(crate) S : {
  "f" : T::ty();
  "g" : candid::func!((List) -> (B, Tree, Stream));
});
candid::define_function!(pub(crate) T : (S) -> ());
type CanisterId = Principal;
#derive[CandidType, Deserialize, Clone]
pub(crate) struct ListInner {
  #[serde(skip_deserializing)]
  #[serde(rename="head")]
  HEAD: candid::Int,
  #[serde(skip_deserializing)]
  tail: Arc<MyList>,
}
#[derive(CandidType, Deserialize, Debug)]
pub(crate) struct MyList(pub(crate) Option<ListInner>);
#[derive(CandidType, Deserialize, Debug)]
pub(crate) struct Nested3 {
  pub(crate) _0_: u128,
  pub(crate) _42_: u128,
  pub(crate) _43_: u8,
}
#[derive(CandidType, Deserialize, Debug)]
pub(crate) enum Nested41 {
  _42_,
  #[serde(skip_deserializing)]
  #[serde(rename="A")]
  AAA,
  B,
  C,
}
#[derive(CandidType, Deserialize, Debug)]
pub(crate) struct Nested {
  pub(crate) _0_: u128,
  pub(crate) _1_: u128,
  pub(crate) _2_: (u128,candid::Int,),
  pub(crate) _3_: Nested3,
  pub(crate) _40_: u128,
  pub(crate) _41_: Nested41,
  pub(crate) _42_: u128,
}
candid::define_service!(pub BrokerReturn : {
  "current" : candid::func!(() -> (u32));
  "up" : candid::func!(() -> ());
});
candid::define_service!(pub(crate) Broker : {
  "find" : candid::func!((String) -> (BrokerReturn));
});
#[derive(CandidType, Deserialize, Debug)]
pub(crate) struct NestedResErrOk { pub(crate) content: String }
pub(crate) type NestedRes = std::result::Result<
  my::Result<(), ()>, another::Result<NestedResErrOk, (candid::Int,)>
>;
#[derive(CandidType, Deserialize, Debug)]
pub(crate) enum HArg1 { A(u128), B(Option<String>) }
#[derive(CandidType, Deserialize, Debug)]
pub(crate) struct HRet42 {}
#[derive(CandidType, Deserialize, Debug)]
pub(crate) struct HRet { pub(crate) _42_: HRet42, pub(crate) id: u128 }
candid::define_function!(pub(crate) FArg1 : (i32) -> (i64));
#[derive(CandidType, Deserialize, Debug)]
pub(crate) struct ResErr { pub(crate) error: String }
pub(crate) type Res = std::result::Result<(candid::Int,u128,), ResErr>;
candid::define_function!(pub(crate) F : (MyList, FArg1) -> (
    Option<MyList>,
    Res,
  ));
#[derive(CandidType, Deserialize, Debug)]
pub(crate) enum A { #[serde(rename="a")] A, #[serde(rename="b")] B(B) }
#[derive(CandidType, Deserialize, Debug)]
pub(crate) struct XRet2Ok { pub(crate) result: String }
#[derive(CandidType, Deserialize, Debug)]
pub(crate) enum Error { #[serde(rename="a")] A, #[serde(rename="b")] B }

pub struct Service(pub Principal);
impl Service {
  pub async fn bbbbb(&self, arg0: &B) -> Result<()> {
    ic_cdk::call(self.0, "bbbbb", (arg0,)).await
  }
  pub async fn f(&self, server: &S) -> Result<()> {
    ic_cdk::call(self.0, "f", (server,)).await
  }
  pub async fn f_1(&self, arg0: &List, test: &serde_bytes::ByteBuf, arg2: &Option<bool>) -> Result<()> {
    ic_cdk::call(self.0, "f1", (arg0,test,arg2,)).await
  }
  pub async fn g(&self, arg0: &List) -> Result<(B,Tree,Stream,)> {
    ic_cdk::call(self.0, "g", (arg0,)).await
  }
  pub async fn G11(&self, id: &CanisterId, list: &MyList, is_okay: &Option<MyList>, arg3: &Nested) -> Result<(i128,Broker,NestedRes,)> {
    ic_cdk::call(self.0, "g1", (id,list,is_okay,arg3,)).await
  }
  pub async fn h(&self, arg0: &Vec<Option<String>>, arg1: &HArg1, arg2: &Option<MyList>) -> Result<(HRet,)> {
    ic_cdk::call(self.0, "h", (arg0,arg1,arg2,)).await
  }
  pub async fn i(&self, arg0: &MyList, arg1: &FArg1) -> Result<(Option<MyList>,Res,)> {
    ic_cdk::call(self.0, "i", (arg0,arg1,)).await
  }
  pub async fn x(&self, arg0: &A, arg1: &B) -> Result<(Option<A>,Option<B>,std::result::Result<XRet2Ok, Error>,)> {
    ic_cdk::call(self.0, "x", (arg0,arg1,)).await
  }
}
pub const CANISTER_ID : Principal = Principal::from_slice(&[]); // aaaaa-aa
pub const service : Service = Service(CANISTER_ID);
#[test]
fn test_Arc_MyList_() {
  // Generated from ListInner.record.tail.use_type = "Arc<MyList>"
  let candid_src = r#"type List = opt ListInner;
type ListInner = record { head : int; tail : List };
(List)"#;
  candid_parser::utils::check_rust_type::<Arc<MyList>>(candid_src).unwrap();
}
#[test]
fn test_i128() {
  // Generated from g1.ret0.use_type = "i128"
  let candid_src = r#"(int)"#;
  candid_parser::utils::check_rust_type::<i128>(candid_src).unwrap();
}

