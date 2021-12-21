// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
use ic_cdk::export::candid::{self, CandidType, Deserialize};
use ic_cdk::api::call::CallResult;

type C = Box<A>;
type B = Option<C>;
#[derive(CandidType, Deserialize)]
struct A(Option<B>);

type Z = Box<A>;
type Y = Z;
type X = Y;
struct SERVICE(candid::Principal);
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
