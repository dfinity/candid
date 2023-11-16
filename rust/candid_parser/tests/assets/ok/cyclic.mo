// This is a generated Motoko binding.
// Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.

module {
  public type A = ?B;
  public type B = ?C;
  public type C = A;
  public type X = Y;
  public type Y = Z;
  public type Z = A;
  public type Self = actor { f : shared (A, B, C, X, Y, Z) -> async () }
}
