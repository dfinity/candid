// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.

#[derive(CandidType, Deserialize)]
struct field_arg0 { test: u16, _1291438163_: u8 }

#[derive(CandidType, Deserialize)]
struct field_ret0 {}

#[derive(CandidType, Deserialize)]
struct fieldnat_arg0 { _2_: candid::Int, _50_: candid::Nat }

#[derive(CandidType, Deserialize)]
enum r#if {
  branch{ val: candid::Int, left: Box<r#if>, right: Box<r#if> },
  leaf(candid::Int),
}

type list = Option<Box<node>>;
#[derive(CandidType, Deserialize)]
struct node { head: candid::Nat, tail: list }

#[derive(CandidType, Deserialize)]
struct o(Option<Box<o>>);

type r#return = candid::Service;
#[derive(CandidType, Deserialize)]
struct stream(Option<Box<stream_inner>>);

#[derive(CandidType, Deserialize)]
struct stream_inner { head: candid::Nat, next: candid::Func }

#[derive(CandidType, Deserialize)]
struct t(candid::Func);

#[derive(CandidType, Deserialize)]
enum variant_arg0 { A, B, C, D(f64) }

struct SERVICE(candid::Principal);
impl SERVICE{
  pub async fn Oneway(&self) -> () {
    ic_cdk::call(self.0, "Oneway", ()).await.unwrap()
  }
  pub async fn f_(&self, arg0: o) -> (o) {
    ic_cdk::call(self.0, "f_", (arg0,)).await.unwrap()
  }
  pub async fn field(&self, arg0: field_arg0) -> (field_ret0) {
    ic_cdk::call(self.0, "field", (arg0,)).await.unwrap()
  }
  pub async fn fieldnat(&self, arg0: fieldnat_arg0) -> ((candid::Int,)) {
    ic_cdk::call(self.0, "fieldnat", (arg0,)).await.unwrap()
  }
  pub async fn oneway(&self, arg0: u8) -> () {
    ic_cdk::call(self.0, "oneway", (arg0,)).await.unwrap()
  }
  pub async fn oneway_(&self, arg0: u8) -> () {
    ic_cdk::call(self.0, "oneway_", (arg0,)).await.unwrap()
  }
  pub async fn query(&self, arg0: Vec<u8>) -> (Vec<u8>) {
    ic_cdk::call(self.0, "query", (arg0,)).await.unwrap()
  }
  pub async fn r#return(&self, arg0: o) -> (o) {
    ic_cdk::call(self.0, "return", (arg0,)).await.unwrap()
  }
  pub async fn service(&self, arg0: r#return) -> () {
    ic_cdk::call(self.0, "service", (arg0,)).await.unwrap()
  }
  pub async fn tuple(&self, arg0: (candid::Int,Vec<u8>,String,)) -> (
    (candid::Int,u8,),
  ) { ic_cdk::call(self.0, "tuple", (arg0,)).await.unwrap() }
  pub async fn variant(&self, arg0: variant_arg0) -> () {
    ic_cdk::call(self.0, "variant", (arg0,)).await.unwrap()
  }
}
