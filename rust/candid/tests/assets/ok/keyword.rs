// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::api::call::CallResult as Result;

#[derive(CandidType, Deserialize)]
pub struct o(Option<Box<o>>);

#[derive(CandidType, Deserialize)]
pub struct field_arg0 { test: u16, _1291438163_: u8 }

#[derive(CandidType, Deserialize)]
pub struct field_ret0 {}

#[derive(CandidType, Deserialize)]
pub struct fieldnat_arg0 {
  _2_: candid::Int,
  #[serde(rename="2")]
  _50_: candid::Nat,
}

#[derive(CandidType, Deserialize)]
pub struct node { head: candid::Nat, tail: Box<list> }

#[derive(CandidType, Deserialize)]
pub struct list(Option<node>);

#[derive(CandidType, Deserialize)]
pub enum r#if {
  branch{ val: candid::Int, left: Box<r#if>, right: Box<r#if> },
  leaf(candid::Int),
}

candid::define_function!(pub stream_inner_next : () -> (stream) query);
#[derive(CandidType, Deserialize)]
pub struct stream_inner { head: candid::Nat, next: stream_inner_next }

#[derive(CandidType, Deserialize)]
pub struct stream(Option<stream_inner>);

candid::define_service!(pub r#return : {
  "f" : t::ty();
  "g" : candid::func!((list) -> (r#if, stream));
});
candid::define_function!(pub t : (r#return) -> ());
#[derive(CandidType, Deserialize)]
pub enum variant_arg0 { A, B, C, D(f64) }

pub struct SERVICE(pub Principal);
impl SERVICE {
  pub async fn Oneway(&self) -> Result<()> {
    ic_cdk::call(self.0, "Oneway", ()).await
  }
  pub async fn f_(&self, arg0: o) -> Result<(o,)> {
    ic_cdk::call(self.0, "f_", (arg0,)).await
  }
  pub async fn field(&self, arg0: field_arg0) -> Result<(field_ret0,)> {
    ic_cdk::call(self.0, "field", (arg0,)).await
  }
  pub async fn fieldnat(&self, arg0: fieldnat_arg0) -> Result<
    ((candid::Int,),)
  > { ic_cdk::call(self.0, "fieldnat", (arg0,)).await }
  pub async fn oneway(&self, arg0: u8) -> Result<()> {
    ic_cdk::call(self.0, "oneway", (arg0,)).await
  }
  pub async fn oneway_(&self, arg0: u8) -> Result<()> {
    ic_cdk::call(self.0, "oneway_", (arg0,)).await
  }
  pub async fn query(&self, arg0: serde_bytes::ByteBuf) -> Result<
    (serde_bytes::ByteBuf,)
  > { ic_cdk::call(self.0, "query", (arg0,)).await }
  pub async fn r#return(&self, arg0: o) -> Result<(o,)> {
    ic_cdk::call(self.0, "return", (arg0,)).await
  }
  pub async fn service(&self, arg0: r#return) -> Result<()> {
    ic_cdk::call(self.0, "service", (arg0,)).await
  }
  pub async fn tuple(
    &self,
    arg0: (candid::Int,serde_bytes::ByteBuf,String,),
  ) -> Result<((candid::Int,u8,),)> {
    ic_cdk::call(self.0, "tuple", (arg0,)).await
  }
  pub async fn variant(&self, arg0: variant_arg0) -> Result<()> {
    ic_cdk::call(self.0, "variant", (arg0,)).await
  }
}
pub const service: SERVICE = SERVICE(Principal::from_slice(&[])); // aaaaa-aa
