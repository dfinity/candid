// This is a generated Motoko binding.
// Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.

module {
  public type List = ?(Int, List);
  public type Profile = { age : Nat8; name : Text };
  /// This is a service comment
  public type Self = (Int, l : List, Profile) -> async actor {
    /// This is a method comment
    get : shared () -> async List;
    set : shared List -> async List;
  }
}
