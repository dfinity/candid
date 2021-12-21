// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
use ic_cdk::export::candid::{self, CandidType, Deserialize};
use ic_cdk::api::call::CallResult;

#[derive(CandidType, Deserialize)]
struct bar_arg0 { #[serde(rename="2")] _50_: candid::Int }

#[derive(CandidType, Deserialize)]
struct baz_arg0 { _2_: candid::Int, #[serde(rename="2")] _50_: candid::Nat }

#[derive(CandidType, Deserialize)]
struct baz_ret0 {}

#[derive(CandidType, Deserialize)]
struct tuple (String,String,)

#[derive(CandidType, Deserialize)]
struct non_tuple { _1_: String, _2_: String }

#[derive(CandidType, Deserialize)]
enum bib_ret0 { _0_(candid::Int) }

#[derive(CandidType, Deserialize)]
struct foo_arg0 { _2_: candid::Int }

#[derive(CandidType, Deserialize)]
struct foo_ret0 { _2_: candid::Int, _2: candid::Int }

struct SERVICE(candid::Principal);
impl SERVICE{
  pub async fn bab(&self, arg0: candid::Int, arg1: candid::Nat) -> CallResult<
    ()
  > { ic_cdk::call(self.0, "bab", (arg0,arg1,)).await }
  pub async fn bar(&self, arg0: bar_arg0) -> CallResult<()> {
    ic_cdk::call(self.0, "bar", (arg0,)).await
  }
  pub async fn bas(&self, arg0: (candid::Int,candid::Int,)) -> CallResult<
    ((String,candid::Nat,),)
  > { ic_cdk::call(self.0, "bas", (arg0,)).await }
  pub async fn baz(&self, arg0: baz_arg0) -> CallResult<(baz_ret0,)> {
    ic_cdk::call(self.0, "baz", (arg0,)).await
  }
  pub async fn bba(&self, arg0: tuple) -> CallResult<(non_tuple,)> {
    ic_cdk::call(self.0, "bba", (arg0,)).await
  }
  pub async fn bib(&self, arg0: (candid::Int,)) -> CallResult<(bib_ret0,)> {
    ic_cdk::call(self.0, "bib", (arg0,)).await
  }
  pub async fn foo(&self, arg0: foo_arg0) -> CallResult<(foo_ret0,)> {
    ic_cdk::call(self.0, "foo", (arg0,)).await
  }
}
