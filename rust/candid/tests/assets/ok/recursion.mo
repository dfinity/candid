// This is a static generated Motoko binding. Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.

type A = B;
type B = ?A;
type list = ?node;
type node = { head : Nat; tail : list };
type s = actor { f : t; g : shared list -> async (B, tree, stream) };
type stream = ?{ head : Nat; next : shared query () -> async stream };
type t = shared s -> async ();
type tree = { #branch : { val : Int; left : tree; right : tree }; #leaf : Int };
type _SERVICE = s
