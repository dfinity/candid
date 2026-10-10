// This is a generated Motoko binding.
// Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.

module {
  public type A = B;
  public type B = ?A;
  public type List = ?Node;
  public type Node = { head : Nat; tail : List };
  /// Doc comment for service id
  public type S = actor { f : T; g : shared List -> async (B, Tree, Stream) };
  public type Stream = ?{ head : Nat; next : shared query () -> async Stream };
  public type T = shared S -> async ();
  public type Tree = {
    #branch : { val : Int; left : Tree; right : Tree };
    #leaf : Int;
  };
  public type Self = S
}
