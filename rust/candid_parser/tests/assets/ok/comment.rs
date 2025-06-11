// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
#![allow(dead_code, unused_imports)]
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::api::call::CallResult as Result;

#[derive(CandidType, Deserialize)]
pub enum A { #[serde(rename="a")] A, #[serde(rename="b")] B(Box<B>) }
#[derive(CandidType, Deserialize)]
pub struct B (pub candid::Int,pub candid::Nat,);
pub type Id = u8;


