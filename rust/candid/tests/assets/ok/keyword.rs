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
  branch{ val: candid::Int, left: r#if, right: r#if },
  leaf(candid::Int),
}

type list = Option<node>
#[derive(CandidType, Deserialize)]
struct node { head: candid::Nat, tail: list }

type o = Option<o>
type r#return = candid::Service
type stream = Option<stream_inner>
#[derive(CandidType, Deserialize)]
struct stream_inner { head: candid::Nat, next: candid::Func }

type t = candid::Func
#[derive(CandidType, Deserialize)]
enum variant_arg0 { A, B, C, D(f64) }

pub trait SERVICE {
  pub fn Oneway() -> ();
  pub fn f_(arg0: o) -> (o);
  pub fn field(arg0: field_arg0) -> (field_ret0);
  pub fn fieldnat(arg0: fieldnat_arg0) -> ((candid::Int,));
  pub fn oneway(arg0: u8) -> ();
  pub fn oneway_(arg0: u8) -> ();
  pub fn query(arg0: Vec<u8>) -> (Vec<u8>);
  pub fn r#return(arg0: o) -> (o);
  pub fn service(arg0: r#return) -> ();
  pub fn tuple(arg0: (candid::Int,Vec<u8>,String,)) -> ((candid::Int,u8,));
  pub fn variant(arg0: variant_arg0) -> ();
}
