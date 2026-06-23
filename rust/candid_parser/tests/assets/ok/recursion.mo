// This is a generated Motoko binding.
// Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.

module {
  public type stream = ?{ head : Nat; next : shared query () -> async stream };
  public type A = B;
  /// Doc comment for service id
  public type s = actor { f : t; g : shared list -> async (B, tree, stream) };
  public type B = ?A;
  public type list = ?node;
  public type tree = {
    #branch : { val : Int; left : tree; right : tree };
    #leaf : Int;
  };
  public type t = shared (server : s) -> async ();
  public type node = { head : Nat; tail : list };
  public type Self = s
}
