// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::api::call::CallResult;

pub type C = Box<A>;
pub type B = Option<C>;
#[derive(CandidType, Deserialize)]
pub struct A(Option<B>);

pub type Z = Box<A>;
pub type Y = Z;
pub type X = Y;
pub struct SERVICE(pub Principal);
impl SERVICE{
  pub async fn f(
    &self,
    arg0: A,
    arg1: B,
    arg2: C,
    arg3: X,
    arg4: Y,
    arg5: Z,
  ) -> CallResult<()> {
    ic_cdk::call(self.0, "f", (arg0,arg1,arg2,arg3,arg4,arg5,)).await
  }
}
pub fn service() -> SERVICE {
  SERVICE(Principal::from_text("aaaaa-aa").unwrap())
}
