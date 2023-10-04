// This is a generated Motoko binding.
// Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.

module {
  public type A = B;
  public type B = ?A;
  public type List = ?{ head : Int; tail : List };
  public type a = { #a; #b : b };
  public type b = (Int, Nat);
  public type broker = actor {
    find : shared Text -> async actor {
        current : shared () -> async Nat32;
        up : shared () -> async ();
      };
  };
  public type f = shared (List, shared Int32 -> async Int64) -> async ?List;
  public type list = ?node;
  public type my_type = Principal;
  public type nested = {
    _0_  : Nat;
    _1_  : Nat;
    _2_  : (Nat, Int);
    _3_  : { _0_  : Nat; _42_  : Nat; _43_  : Nat8 };
    _40_  : Nat;
    _41_  : { #_42_ ; #A; #B; #C };
    _42_  : Nat;
  };
  public type node = { head : Nat; tail : list };
  public type s = actor { f : t; g : shared list -> async (B, tree, stream) };
  public type stream = ?{ head : Nat; next : shared query () -> async stream };
  public type t = shared s -> async ();
  public type tree = {
    #branch : { val : Int; left : tree; right : tree };
    #leaf : Int;
  };
  public type Self = actor {
    f : shared (list, Blob, ?Bool) -> ();
    g : shared query (my_type, List, ?List, nested) -> async (Int, broker);
    h : shared ([?Text], { #A : Nat; #B : ?Text }, ?List) -> async {
        _42_  : {};
        id : Nat;
      };
    i : f;
    x : shared composite query (a, b) -> async (?a, ?b);
  }
}
