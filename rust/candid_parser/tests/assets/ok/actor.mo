// This is a generated Motoko binding.
// Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.

module {
  public type doubleNestedOpt = ???Text;
  public type f = shared Int8 -> async Int8;
  public type g = f;
  public type h = shared f -> async f;
  public type nestedOpt = ??Text;
  public type normalOpt = ?Text;
  public type recursiveOpt = ?recursiveOpt;
  public type Self = actor {
    doubleNestedOpt : shared doubleNestedOpt -> async doubleNestedOpt;
    f : shared Nat -> async h;
    g : f;
    h : g;
    nestedOpt : shared nestedOpt -> async nestedOpt;
    normalOpt : shared normalOpt -> async normalOpt;
    recursiveOpt : shared recursiveOpt -> async recursiveOpt;
  }
}
