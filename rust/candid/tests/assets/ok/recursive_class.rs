// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.

#[derive(CandidType, Deserialize)]
struct s(candid::Service);

struct SERVICE(candid::Principal);
impl SERVICE{
  pub async fn next(&self) -> (s) {
    ic_cdk::call(self.0, "next", ()).await.unwrap()
  }
}
