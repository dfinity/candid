// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.

#[derive(CandidType, Deserialize)]
struct bar_arg0 { _50_: candid::Int }

#[derive(CandidType, Deserialize)]
struct baz_arg0 { _2_: candid::Int, _50_: candid::Nat }

#[derive(CandidType, Deserialize)]
struct baz_ret0 {}

#[derive(CandidType, Deserialize)]
enum bib_ret0 { _0_(candid::Int) }

#[derive(CandidType, Deserialize)]
struct foo_arg0 { _2_: candid::Int }

#[derive(CandidType, Deserialize)]
struct foo_ret0 { _2_: candid::Int, _2: candid::Int }

#[derive(CandidType, Deserialize)]
struct non_tuple { _1_: String, _2_: String }

#[derive(CandidType, Deserialize)]
struct tuple (String,String,)

pub trait SERVICE {
  pub fn bab(arg0: candid::Int, arg1: candid::Nat) -> ();
  pub fn bar(arg0: bar_arg0) -> ();
  pub fn bas(arg0: (candid::Int,candid::Int,)) -> ((String,candid::Nat,));
  pub fn baz(arg0: baz_arg0) -> (baz_ret0);
  pub fn bba(arg0: tuple) -> (non_tuple);
  pub fn bib(arg0: (candid::Int,)) -> (bib_ret0);
  pub fn foo(arg0: foo_arg0) -> (foo_ret0);
}
