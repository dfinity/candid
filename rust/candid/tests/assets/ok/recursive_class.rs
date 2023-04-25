// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::api::call::CallResult;

candid::define_service!(pub s : { "next" : candid::func!(() -> (s)) });
pub struct SERVICE(pub Principal);
impl SERVICE{
  pub async fn next(&self) -> CallResult<(s,)> {
    ic_cdk::call(self.0, "next", ()).await
  }
}
pub fn service() -> SERVICE {
  SERVICE(Principal::from_text("aaaaa-aa").unwrap())
}
