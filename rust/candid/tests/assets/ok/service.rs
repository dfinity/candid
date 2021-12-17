// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.

type Func = candid::Func;
#[derive(CandidType, Deserialize)]
struct Service(candid::Service)

type Service2 = Box<Service>;
#[derive(CandidType, Deserialize)]
enum asVariant_ret0 { a(Service2), b{ f: Option<Func> } }

pub trait SERVICE {
  pub fn asArray() -> (Vec<Service2>, Vec<Func>);
  pub fn asPrincipal() -> (Service2, Func);
  pub fn asRecord() -> ((Service2,Option<Service>,Func,));
  pub fn asVariant() -> (asVariant_ret0);
}
