// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
#![allow(dead_code, unused_imports)]
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::api::call::CallResult as Result;

/// PascalCase output collides with a verbatim env key — foo_baz should fall back.
pub type FooBaz = candid::Nat;
pub type FooBar = String;
/// Two names that map to the same PascalCase form — first alphabetically wins, second falls back.
pub type FooBar = candid::Nat;
pub type FooBaz = String;


