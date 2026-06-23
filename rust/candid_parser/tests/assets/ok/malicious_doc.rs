// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.
#![allow(dead_code, unused_imports)]
use candid::{self, CandidType, Deserialize, Principal};
use ic_cdk::api::call::CallResult as Result;

/// */ import { malicious } from 'attacker'; console.log('injected!'); /*
/// Normal doc line
/// Another */ attempt /* to inject
#[derive(CandidType, Deserialize)]
pub struct MaliciousType {
  /// Doc comment for field with */ malicious code /* in it
  pub field: String,
}

/// Service with */ malicious */ doc
pub struct Service(pub Principal);
impl Service {
  /// Method with */ in doc comment
  pub async fn get(&self) -> Result<(MaliciousType,)> {
    ic_cdk::call(self.0, "get", ()).await
  }
}
/// Canister ID: `aaaaa-aa`
pub const CANISTER_ID : Principal = Principal::from_slice(&[]);
pub const service : Service = Service(CANISTER_ID);

