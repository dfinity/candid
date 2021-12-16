// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.

#[derive(CandidType, Deserialize)]
struct t {
  _34_: candid::Nat,
  _39_: candid::Nat,
  _7621_: candid::Nat,
  _1020746185_: candid::Nat,
};

pub trait SERVICE { pub fn _2635468193_(arg0: t) -> (); }
