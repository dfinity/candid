// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
#![allow(dead_code, unused_imports)]
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::api::call::CallResult as Result;

#[derive(CandidType, Deserialize)]
pub struct CallbacksAreFun {
  pub inline_callback: Box<CallbacksAreFunInlineCallback>,
  pub callback: Box<Fn>,
}
candid::define_function!(pub CallbacksAreFunInlineCallback : (candid::Nat) -> (
    candid::Nat,
  ));
candid::define_function!(pub Fn : (candid::Nat) -> (candid::Nat) query);


