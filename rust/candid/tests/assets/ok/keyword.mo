// This is a generated Motoko binding. Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.

type if_ = { #branch : { val : Int; left : if_; right : if_ }; #leaf : Int };
type list = ?node;
type node = { head : Nat; tail : list };
type o = ?o;
type return_ = actor { f : t; g : shared list -> async (if_, stream) };
type stream = ?{ head : Nat; next : shared query () -> async stream };
type t = shared return_ -> async ();
type _SERVICE = actor {
  Oneway : shared () -> ();
  f__ : shared o -> async o;
  field : shared { test : Nat16; _1291438163_  : Nat8 } -> async {};
  fieldnat : shared { _2_  : Int; _50_ : Nat } -> async { _0_  : Int };
  oneway : shared Nat8 -> ();
  oneway__ : shared Nat8 -> ();
  query_ : shared query Blob -> async [Nat8];
  return_ : shared o -> async o;
  service : t;
  tuple : shared ((Int, Blob, Text)) -> async ((Int, Nat8));
  variant : shared { #A; #B; #C; #D : Float } -> async ();
}
