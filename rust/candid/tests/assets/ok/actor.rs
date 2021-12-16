// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.

type f = candid::Func;
type g = f;
type h = candid::Func;
#[derive(CandidType, Deserialize)]
struct o(Option<Box<o>>);

pub trait SERVICE {
  pub fn f(arg0: candid::Nat) -> (h);
  pub fn g(arg0: i8) -> (i8);
  pub fn h(arg0: i8) -> (i8);
  pub fn o(arg0: o) -> (o);
}
