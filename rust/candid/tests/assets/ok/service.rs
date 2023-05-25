// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::api::call::CallResult as Result;

candid::define_function!(pub Func : () -> (Service));
candid::define_service!(pub Service : { "f" : Func::ty() });
pub type Service2 = Box<Service>;
#[derive(CandidType, Deserialize)]
pub enum asVariant_ret0 { a(Service2), b{ f: Option<Func> } }

pub struct SERVICE(pub Principal);
impl SERVICE {
  pub async fn asArray(&self) -> Result<(Vec<Service2>,Vec<Func>,)> {
    ic_cdk::call(self.0, "asArray", ()).await
  }
  pub async fn asPrincipal(&self) -> Result<(Service2,Func,)> {
    ic_cdk::call(self.0, "asPrincipal", ()).await
  }
  pub async fn asRecord(&self) -> Result<((Service2,Option<Service>,Func,),)> {
    ic_cdk::call(self.0, "asRecord", ()).await
  }
  pub async fn asVariant(&self) -> Result<(asVariant_ret0,)> {
    ic_cdk::call(self.0, "asVariant", ()).await
  }
}
pub const service: SERVICE = SERVICE(Principal::from_slice(&[])); // aaaaa-aa
