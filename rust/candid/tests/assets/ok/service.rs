// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
use ic_cdk::export::candid::{self, CandidType, Deserialize};
use ic_cdk::api::call::CallResult;

type Func = candid::Func;
#[derive(CandidType, Deserialize)]
struct Service(candid::Service);

type Service2 = Box<Service>;
#[derive(CandidType, Deserialize)]
enum asVariant_ret0 { a(Service2), b{ f: Option<Func> } }

struct SERVICE(candid::Principal);
impl SERVICE{
  pub async fn asArray(&self) -> CallResult<(Vec<Service2>,Vec<Func>,)> {
    ic_cdk::call(self.0, "asArray", ()).await
  }
  pub async fn asPrincipal(&self) -> CallResult<(Service2,Func,)> {
    ic_cdk::call(self.0, "asPrincipal", ()).await
  }
  pub async fn asRecord(&self) -> CallResult<
    ((Service2,Option<Service>,Func,),)
  > { ic_cdk::call(self.0, "asRecord", ()).await }
  pub async fn asVariant(&self) -> CallResult<(asVariant_ret0,)> {
    ic_cdk::call(self.0, "asVariant", ()).await
  }
}
