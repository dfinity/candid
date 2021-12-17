// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.

#[derive(CandidType, Deserialize)]
struct t {
  _34_: candid::Nat,
  _39_: candid::Nat,
  _7621_: candid::Nat,
  _1020746185_: candid::Nat,
}

struct SERVICE(candid::Principal);
impl SERVICE{
  pub async fn _2635468193_(&self, arg0: t) -> () {
    ic_cdk::call(self.0, "\n\'\"\'\'\"\"\r\t", (arg0,)).await.unwrap()
  }
}
