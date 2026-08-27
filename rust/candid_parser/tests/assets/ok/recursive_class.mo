// This is a generated Motoko binding.
// Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.

module {
  public type S = actor { next : shared () -> async S };
  public type Self = S -> async S
}
