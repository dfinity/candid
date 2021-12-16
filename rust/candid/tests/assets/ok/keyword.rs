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

