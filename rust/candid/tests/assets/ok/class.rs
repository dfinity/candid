// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.

#[derive(CandidType, Deserialize)]
struct List(Option<(candid::Int,List,)>);

pub trait SERVICE {
  pub fn get() -> (List);
  pub fn set(arg0: List) -> (List);
}
