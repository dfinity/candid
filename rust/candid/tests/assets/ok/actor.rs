// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.

type f = candid::Func;
type h = candid::Func;
type g = f;
#[derive(CandidType, Deserialize)]
struct o(Option<Box<o>>);

struct SERVICE(candid::Principal);
impl SERVICE{
  pub async fn f(&self, arg0: candid::Nat) -> (h) {
    ic_cdk::call(self.0, "f", (arg0,)).await.unwrap()
  }
  pub async fn g(&self, arg0: i8) -> (i8) {
    ic_cdk::call(self.0, "g", (arg0,)).await.unwrap()
  }
  pub async fn h(&self, arg0: i8) -> (i8) {
    ic_cdk::call(self.0, "h", (arg0,)).await.unwrap()
  }
  pub async fn o(&self, arg0: o) -> (o) {
    ic_cdk::call(self.0, "o", (arg0,)).await.unwrap()
  }
}
