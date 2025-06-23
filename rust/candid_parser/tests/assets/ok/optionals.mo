// This is a generated Motoko binding.
// Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.

module {
  public type doubleNested_opt = ???Text;
  public type nested_opt = ??Text;
  public type normal_opt = ?Text;
  public type recursive_opt = ?recursive_opt;
  public type Self = actor {
    doubleNested_opt : shared doubleNested_opt -> async doubleNested_opt;
    nested_opt : shared nested_opt -> async nested_opt;
    normal_opt : shared normal_opt -> async normal_opt;
    recursive_opt : shared recursive_opt -> async recursive_opt;
  }
}
