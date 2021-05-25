type non_tuple = { _1_  : Text; _2_  : Text };
type tuple = (Text, Text);
public type _MAIN = {
  bab : shared (Int, Nat) -> async ();
  bar : shared { _50_ : Int } -> async ();
  bas : shared (Int, Int) -> async (Text, Nat);
  baz : shared { _2_  : Int; _50_ : Nat } -> async {};
  bba : shared tuple -> async non_tuple;
  bib : shared { _0_  : Int } -> async { #_0_  : Int };
  foo : shared { _2_  : Int } -> async { _2_  : Int; _2 : Int };
}
