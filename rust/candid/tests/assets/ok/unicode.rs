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

pub trait SERVICE {
  pub fn _0_(arg0: candid::Nat) -> (candid::Nat);
  pub fn _356566390_() -> ();
  pub fn _3300066460_(arg0: A) -> (B);
  pub fn _2669435454_(arg0: candid::Nat) -> (candid::Nat);
}
