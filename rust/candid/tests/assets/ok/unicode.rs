// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.

#[derive(CandidType, Deserialize)]
struct A {
  _11864174_: candid::Nat,
  _1832283146_: candid::Nat,
  _2119362116_: candid::Nat,
  _3133479156_: candid::Nat,
}

#[derive(CandidType, Deserialize)]
enum B { _0_, _650764729_, _1036827129_, _3099250646_ }

struct SERVICE(candid::Principal);
impl SERVICE{
  pub async fn _0_(&self, arg0: candid::Nat) -> (candid::Nat) {
    ic_cdk::call(self.0, "", (arg0,)).await.unwrap()
  }
  pub async fn _356566390_(&self) -> () {
    ic_cdk::call(self.0, "✈️  🚗 ⛱️ ", ()).await.unwrap()
  }
  pub async fn _3300066460_(&self, arg0: A) -> (B) {
    ic_cdk::call(self.0, "函数名", (arg0,)).await.unwrap()
  }
  pub async fn _2669435454_(&self, arg0: candid::Nat) -> (candid::Nat) {
    ic_cdk::call(self.0, "👀", (arg0,)).await.unwrap()
  }
}
