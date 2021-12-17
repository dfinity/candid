// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.

type Func = candid::Func;
#[derive(CandidType, Deserialize)]
struct Service(candid::Service);

type Service2 = Box<Service>;
#[derive(CandidType, Deserialize)]
enum asVariant_ret0 { a(Service2), b{ f: Option<Func> } }

struct SERVICE(candid::Principal);
impl SERVICE{
  pub async fn asArray(&self) -> (Vec<Service2>, Vec<Func>) {
    ic_cdk::call(self.0, "asArray", ()).await.unwrap()
  }
  pub async fn asPrincipal(&self) -> (Service2, Func) {
    ic_cdk::call(self.0, "asPrincipal", ()).await.unwrap()
  }
  pub async fn asRecord(&self) -> ((Service2,Option<Service>,Func,)) {
    ic_cdk::call(self.0, "asRecord", ()).await.unwrap()
  }
  pub async fn asVariant(&self) -> (asVariant_ret0) {
    ic_cdk::call(self.0, "asVariant", ()).await.unwrap()
  }
}
