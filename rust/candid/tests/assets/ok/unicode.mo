// This is a generated Motoko binding. Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.

type A = {
  _11864174_ : Nat;
  _1832283146_ : Nat;
  _2119362116_ : Nat;
  _3133479156_ : Nat;
};
type B = { #_0_; #_650764729_; #_1036827129_; #_3099250646_ };
type _SERVICE = actor {
  _0_ : shared Nat -> async Nat;
  _356566390_ : shared () -> ();
  _3300066460_ : shared A -> async B;
  _2669435454_ : shared query Nat -> async Nat;
}
