// This is a generated Motoko binding.
// Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.

module {
  /// */ import { malicious } from 'attacker'; console.log('injected!'); /*
  /// Normal doc line
  /// Another */ attempt /* to inject
  public type MaliciousType = {
    /// Doc comment for field with */ malicious code /* in it
    field : Text;
  };
  /// Service with */ malicious */ doc
  public type Self = actor {
    /// Method with */ in doc comment
    get : shared query () -> async MaliciousType;
  }
}
