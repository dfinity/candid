// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
#![allow(dead_code, unused_imports)]
use candid::{self, CandidType, Deserialize, Principal};

#[derive(CandidType, Deserialize)]
pub struct List(pub Option<(candid::Int,Box<List>,)>);
#[derive(CandidType, Deserialize)]
pub struct Profile { pub age: u8, pub name: String }

#[ic_cdk::init]
fn init(arg0: candid::Int, l: List, arg2: Profile) {
  unimplemented!()
}
#[ic_cdk::update]
fn get() -> List {
  unimplemented!()
}
#[ic_cdk::update]
fn set(arg0: List) -> List {
  unimplemented!()
}
#[link_section = "icp:public candid:service"]
pub static __SERVICE: [u8; 94] = *br#"type List = opt record { int; List };
service : { get : () -> (List); set : (List) -> (List) }"#;

