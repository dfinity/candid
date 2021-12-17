// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.

#[derive(CandidType, Deserialize)]
struct List(Option<(candid::Int,Box<List>,)>);

struct SERVICE(candid::Principal);
impl SERVICE{
  pub async fn get(&self) -> (List) {
    ic_cdk::call(self.0, "get", ()).await.unwrap()
  }
  pub async fn set(&self, arg0: List) -> (List) {
    ic_cdk::call(self.0, "set", (arg0,)).await.unwrap()
  }
}
