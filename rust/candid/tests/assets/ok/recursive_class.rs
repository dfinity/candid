// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.

#[derive(CandidType, Deserialize)]
struct s(candid::Service)

pub trait SERVICE { pub fn next() -> (s); }
