// This is a generated Motoko binding.
// Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.

module {
  public type T = { _0_  : T };
  public type Self = actor {
    f : shared {} -> async {#};
    g : shared T -> async { #a : T };
    h : shared ((T, None)) -> async { #a : T; #b : {} };
  }
}
