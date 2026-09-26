// This is a generated Motoko binding.
// Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.

module {
  public type F = shared Int8 -> async Int8;
  public type G = F;
  public type H = shared F -> async F;
  public type O = ?O;
  public type Self = actor {
    f : shared Nat -> async H;
    g : F;
    h : G;
    h2 : H;
    o : shared O -> async O;
  }
}
