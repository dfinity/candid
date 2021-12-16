// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.

type Func = candid::Func
type Service = candid::Service
type Service2 = Service
#[derive(CandidType, Deserialize)]
enum asVariant_ret0 { a(Service2), b{ f: Option<Func> } }

