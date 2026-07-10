// This is a generated Motoko binding.
// Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.

module {
  /// PascalCase output collides with a verbatim env key — foo_baz should fall back.
  public type FooBaz = Nat;
  public type FooBar = Text;
  /// Two names that map to the same PascalCase form — first alphabetically wins, second falls back.
  public type foo_bar = Nat;
  public type foo_baz = Text;

}
