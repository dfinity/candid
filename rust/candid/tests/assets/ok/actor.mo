// This is a generated Motoko binding. Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.

type f = shared Int8 -> async Int8;
type g = f;
type h = shared f -> async f;
type o = ?o;
type _SERVICE = actor {
  f : shared Nat -> async h;
  g : f;
  h : g;
  o : shared o -> async o;
}
