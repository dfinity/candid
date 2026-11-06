// This is a generated Motoko binding.
// Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.

module {
  public type If = {
    #branch : { val : Int; left : If; right : If };
    #leaf : Int;
  };
  public type List = ?Node;
  public type Node = { head : Nat; tail : List };
  public type O = ?O;
  public type Return = actor { f : T; g : shared List -> async (If, Stream) };
  public type Stream = ?{ head : Nat; next : shared query () -> async Stream };
  public type T = shared Return -> async ();
  public type Self = actor {
    Oneway : shared () -> ();
    f__ : shared O -> async O;
    field : shared { test : Nat16; _1291438163_  : Nat8 } -> async {};
    fieldnat : shared { _2_  : Int; _50_ : Nat } -> async { _0_  : Int };
    oneway : shared Nat8 -> ();
    oneway__ : shared Nat8 -> ();
    query_ : shared query Blob -> async Blob;
    return_ : shared O -> async O;
    service : T;
    tuple : shared ((Int, Blob, Text)) -> async ((Int, Nat8));
    variant : shared { #A; #B; #C; #D : Float } -> async ();
  }
}
