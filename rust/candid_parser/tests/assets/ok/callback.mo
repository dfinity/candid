// This is a generated Motoko binding.
// Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.

module {
  public type CallbacksAreFun = {
    inline_callback : shared Nat -> async Nat;
    callback : Fn;
  };
  public type Fn = shared query Nat -> async Nat;

}
