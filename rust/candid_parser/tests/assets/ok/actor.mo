// This is a generated Motoko binding.
// Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.

module {
  public type f = shared Int8 -> async Int8;
  public type g = f;
  public type h = shared f -> async f;
  public type o = ?o;
  public type Self = actor {
    f : shared Nat -> async h;
    g : f;
    h : g;
    h2 : h;
    o : shared o -> async o;
  }
}
