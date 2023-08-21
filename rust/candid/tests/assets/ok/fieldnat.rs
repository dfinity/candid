// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::api::call::CallResult as Result;

#[derive(CandidType, Deserialize)]
pub struct BarArg { #[serde(rename="2")] _50_: candid::Int }

#[derive(CandidType, Deserialize)]
pub enum BarRet { #[serde(rename="e20")] E20, #[serde(rename="e30")] E30 }

#[derive(CandidType, Deserialize)]
pub struct BazArg { _2_: candid::Int, #[serde(rename="2")] _50_: candid::Nat }

#[derive(CandidType, Deserialize)]
pub struct BazRet {}

#[derive(CandidType, Deserialize)]
pub struct Tuple (String,String,);

#[derive(CandidType, Deserialize)]
pub struct NonTuple { _1_: String, _2_: String }

#[derive(CandidType, Deserialize)]
pub enum BibRet { _0_(candid::Int) }

#[derive(CandidType, Deserialize)]
pub struct FooArg { _2_: candid::Int }

#[derive(CandidType, Deserialize)]
pub struct FooRet { _2_: candid::Int, _2: candid::Int }

pub struct SERVICE(pub Principal);
impl SERVICE {
  pub async fn bab(&self, arg0: candid::Int, arg1: candid::Nat) -> Result<()> {
    ic_cdk::call(self.0, "bab", (arg0,arg1,)).await
  }
  pub async fn bar(&self, arg0: BarArg) -> Result<(BarRet,)> {
    ic_cdk::call(self.0, "bar", (arg0,)).await
  }
  pub async fn bas(&self, arg0: (candid::Int,candid::Int,)) -> Result<
    ((String,candid::Nat,),)
  > { ic_cdk::call(self.0, "bas", (arg0,)).await }
  pub async fn baz(&self, arg0: BazArg) -> Result<(BazRet,)> {
    ic_cdk::call(self.0, "baz", (arg0,)).await
  }
  pub async fn bba(&self, arg0: Tuple) -> Result<(NonTuple,)> {
    ic_cdk::call(self.0, "bba", (arg0,)).await
  }
  pub async fn bib(&self, arg0: (candid::Int,)) -> Result<(BibRet,)> {
    ic_cdk::call(self.0, "bib", (arg0,)).await
  }
  pub async fn foo(&self, arg0: FooArg) -> Result<(FooRet,)> {
    ic_cdk::call(self.0, "foo", (arg0,)).await
  }
}
pub const service: SERVICE = SERVICE(Principal::from_slice(&[])); // aaaaa-aa
