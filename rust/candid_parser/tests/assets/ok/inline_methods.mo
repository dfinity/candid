// This is a generated Motoko binding.
// Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.

module {
  public type Fn = shared query Nat -> async Nat;
  public type Gn = Fn;
  public type R = { x : Nat; fn : Fn; gn : Gn; nested : { fn : Gn } };
  public type RInline = { x : Nat; fn : shared query Nat -> async Nat };
  public type Self = actor {
    add_two : shared Nat -> async Nat;
    fn : Fn;
    high_order_fn : shared (Nat, Fn) -> async Nat;
    high_order_fn_inline : shared (
        Nat,
        shared query Nat -> async Nat,
      ) -> async Nat;
    high_order_fn_via_id : shared (Nat, Gn) -> async Fn;
    high_order_fn_via_record : shared R -> async Nat;
    high_order_fn_via_record_inline : shared RInline -> async Nat;
  }
}
