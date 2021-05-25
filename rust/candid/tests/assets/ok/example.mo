type List = ?{ head : Int; tail : List };
type broker = actor {
  find : shared Text -> async actor {
      current : shared () -> async Nat32;
      up : shared () -> async ();
    };
};
type f = shared (List, shared Int32 -> async Int64) -> async ?List;
type my_type = Principal;
type nested = {
  _0_  : Nat;
  _1_  : Nat;
  _2_  : (Nat, Int);
  _3_  : { _0_  : Nat; _42_  : Nat; _43_  : Nat8 };
  _40_  : Nat;
  _41_  : { #_42_ ; #A; #B; #C };
  _42_  : Nat;
};
public type _MAIN = {
  f : shared ([Nat8], ?Bool) -> ();
  g : shared query (my_type, List, ?List, nested) -> async (Int, broker);
  h : shared ([?Text], { #A : Nat; #B : ?Text }, ?List) -> async {
      _42_  : {};
      id : Nat;
    };
  i : f;
}
