// This is a generated Motoko binding.
// Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.

module {
  public type option2 = ?option1;
  public type nested = ??Nat;
  public type option1 = ?Nat;
  public type option3 = ?option2;
  public type Self = actor { f : shared () -> async (option1, option2) }
}
