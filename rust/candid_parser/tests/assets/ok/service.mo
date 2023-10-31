// This is a generated Motoko binding.
// Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.

module {
  public type Func = shared () -> async Service;
  public type Service = actor { f : Func };
  public type Service2 = Service;
  public type Self = actor {
    asArray : shared query () -> async ([Service2], [Func]);
    asPrincipal : shared () -> async (Service2, Func);
    asRecord : shared () -> async ((Service2, ?Service, Func));
    asVariant : shared () -> async { #a : Service2; #b : { f : ?Func } };
  }
}
