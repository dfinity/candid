// This is a generated Motoko binding.
// Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.

module {
  public type if_ = {
    #branch : { val : Int; left : if_; right : if_ };
    #leaf : Int;
  };
  public type list = ?node;
  public type node = { head : Nat; tail : list };
  public type o = ?o;
  public type return_ = actor { f : t; g : shared list -> async (if_, stream) };
  public type stream = ?{ head : Nat; next : shared query () -> async stream };
  public type t = shared (server : return_) -> async ();
  public type Self = actor {
    Oneway : shared () -> ();
    f__ : shared o -> async o;
    field : shared { test : Nat16; _1291438163_  : Nat8 } -> async {};
    fieldnat : shared { _2_  : Int; _50_ : Nat } -> async { _0_  : Int };
    oneway : shared Nat8 -> ();
    oneway__ : shared Nat8 -> ();
    query_ : shared query Blob -> async Blob;
    return_ : shared o -> async o;
    service : t;
    tuple : shared ((Int, Blob, Text)) -> async ((Int, Nat8));
    variant : shared { #A; #B; #C; #D : Float } -> async ();
  }
}
