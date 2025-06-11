// This is a generated Motoko binding.
// Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.

module {
  public type non_tuple = { _1_  : Text; _2_  : Text };
  public type tuple = (Text, Text);
  public type Self = actor {
    bab : shared (two : Int, Nat) -> async ();
    bar : shared { _50_ : Int } -> async { #e20; #e30 };
    bas : shared ((Int, Int)) -> async ((Text, Nat));
    baz : shared { _2_  : Int; _50_ : Nat } -> async {};
    bba : shared tuple -> async non_tuple;
    bib : shared { _0_  : Int } -> async { #_0_  : Int };
    foo : shared { _2_  : Int } -> async { _2_  : Int; _2 : Int };
  }
}
