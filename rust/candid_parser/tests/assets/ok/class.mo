// This is a generated Motoko binding.
// Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.

module {
  public type List = ?(Int, List);
  public type Profile = { age : Nat8; name : Text };
  /// Doc comment for class service
  public type Self = (Int, List, Profile) -> async actor {
    /// Doc comment for get method in class service
    get : shared () -> async List;
    set : shared List -> async List;
  }
}
