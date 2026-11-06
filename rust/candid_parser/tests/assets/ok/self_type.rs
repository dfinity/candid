// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
#![allow(dead_code, unused_imports)]
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::api::call::CallResult as Result;

/// Verbatim "Self" in env — falls back to "Self_" to avoid shadowing pp_actor output.
pub type Self_ = String;
/// "self" would PascalCase to "Self" which is reserved — falls back to "self".
pub type Self_ = candid::Nat;


