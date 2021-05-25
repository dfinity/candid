// This is a static generated Motoko binding. Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.

type list = ?node;
type node = { head : Nat; tail : list };
type o = ?o;
type s = actor { f : t; g : shared list -> async (tree, stream) };
type stream = ?{ head : Nat; next : shared query () -> async stream };
type t = shared s -> async ();
type tree = { #branch : { val : Int; left : tree; right : tree }; #leaf : Int };
type _SERVICE = actor {
  f__ : shared o -> async o;
  field : shared { test : Nat16; _1291438163_  : Nat8 } -> async {};
  fieldnat : shared { _2_  : Int; _50_ : Nat } -> async { _0_  : Int };
  oneway : shared Nat8 -> ();
  oneway__ : shared Nat8 -> ();
  query_ : shared query [Nat8] -> async [Nat8];
  return_ : shared o -> async o;
  service : t;
  tuple : shared (Int, [Nat8], Text) -> async (Int, Nat8);
  variant : shared { #A; #B; #C; #D : Float } -> async ();
}
