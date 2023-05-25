// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::api::call::CallResult as Result;

#[derive(CandidType, Deserialize)]
pub struct bar_arg0 { #[serde(rename="2")] _50_: candid::Int }

#[derive(CandidType, Deserialize)]
pub enum bar_ret0 { e20, e30 }

#[derive(CandidType, Deserialize)]
pub struct baz_arg0 { _2_: candid::Int, #[serde(rename="2")] _50_: candid::Nat }

#[derive(CandidType, Deserialize)]
pub struct baz_ret0 {}

#[derive(CandidType, Deserialize)]
pub struct tuple (String,String,);

#[derive(CandidType, Deserialize)]
pub struct non_tuple { _1_: String, _2_: String }

#[derive(CandidType, Deserialize)]
pub enum bib_ret0 { _0_(candid::Int) }

#[derive(CandidType, Deserialize)]
pub struct foo_arg0 { _2_: candid::Int }

#[derive(CandidType, Deserialize)]
pub struct foo_ret0 { _2_: candid::Int, _2: candid::Int }

pub struct SERVICE(pub Principal);
impl SERVICE {
  pub async fn bab(&self, arg0: candid::Int, arg1: candid::Nat) -> Result<()> {
    ic_cdk::call(self.0, "bab", (arg0,arg1,)).await
  }
  pub async fn bar(&self, arg0: bar_arg0) -> Result<(bar_ret0,)> {
    ic_cdk::call(self.0, "bar", (arg0,)).await
  }
  pub async fn bas(&self, arg0: (candid::Int,candid::Int,)) -> Result<
    ((String,candid::Nat,),)
  > { ic_cdk::call(self.0, "bas", (arg0,)).await }
  pub async fn baz(&self, arg0: baz_arg0) -> Result<(baz_ret0,)> {
    ic_cdk::call(self.0, "baz", (arg0,)).await
  }
  pub async fn bba(&self, arg0: tuple) -> Result<(non_tuple,)> {
    ic_cdk::call(self.0, "bba", (arg0,)).await
  }
  pub async fn bib(&self, arg0: (candid::Int,)) -> Result<(bib_ret0,)> {
    ic_cdk::call(self.0, "bib", (arg0,)).await
  }
  pub async fn foo(&self, arg0: foo_arg0) -> Result<(foo_ret0,)> {
    ic_cdk::call(self.0, "foo", (arg0,)).await
  }
}
pub const service: SERVICE = SERVICE(Principal::from_slice(&[])); // aaaaa-aa
