// This is a generated Motoko binding.
// Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.

module {
  public type A = B;
  public type B = ?A;
  /// Doc comment for List
  public type List = ?{
    /// Doc comment for List head
    head : Int;
    /// Doc comment for List tail
    tail : List;
  };
  public type a = { #a; #b : b };
  public type b = (Int, Nat);
  /// Doc comment for broker service
  public type broker = actor {
    find : shared (name : Text) -> async actor {
        current : shared () -> async Nat32;
        up : shared () -> async ();
      };
  };
  public type f = shared (List, shared Int32 -> async Int64) -> async (
      ?List,
      res,
    );
  public type list = ?node;
  /// Doc comment for prim type
  public type my_type = Principal;
  public type my_variant = {
    /// Doc comment for my_variant field a
    #a : {
      /// Doc comment for my_variant field a field b
      b : Text;
    };
    /// Doc comment for my_variant field c
    #c : ?{
      /// Doc comment for my_variant field c field d
      d : Text;
    };
  };
  /// Doc comment for nested type
  public type nested = {
    _0_  : Nat;
    _1_  : Nat;
    /// Doc comment for nested record
    _2_  : (Nat, Int);
    _3_  : { _0_  : Nat; _42_  : Nat; _43_  : Nat8 };
    _40_  : Nat;
    _41_  : { #_42_ ; #A; #B; #C };
    _42_  : Nat;
  };
  /// Doc comment for nested_records
  public type nested_records = {
    /// Doc comment for nested_records field nested
    nested : ?{
      /// Doc comment for nested_records field nested_field
      nested_field : Text;
    };
  };
  public type nested_res = {
    #Ok : { #Ok; #Err };
    #Err : {
      /// Doc comment for Ok in nested variant
      #Ok : { content : Text };
      /// Doc comment for Err in nested variant
      #Err : { _0_  : Int };
    };
  };
  public type node = { head : Nat; tail : list };
  /// Doc comment for res type
  public type res = {
    /// Doc comment for Ok variant
    #Ok : (Int, Nat);
    /// Doc comment for Err variant
    #Err : {
      /// Doc comment for error field in Err variant,
      /// on multiple lines
      error : Text;
    };
  };
  /// Doc comment for service id
  public type s = actor { f : t; g : shared list -> async (B, tree, stream) };
  public type stream = ?{ head : Nat; next : shared query () -> async stream };
  public type t = shared (server : s) -> async ();
  public type tree = {
    #branch : { val : Int; left : tree; right : tree };
    #leaf : Int;
  };
  /// Doc comment for service
  public type Self = actor {
    /// Doc comment for f1 method of service
    f1 : shared (list, test : Blob, ?Bool) -> ();
    g1 : shared query (my_type, List, ?List, nested) -> async (
        Int,
        broker,
        nested_res,
      );
    h : shared ([?Text], { #A : Nat; #B : ?Text }, ?List) -> async {
        _42_  : {};
        id : Nat;
      };
    /// Doc comment for i method of service
    i : f;
    x : shared composite query (a, b) -> async (
        ?a,
        ?b,
        { #Ok : { result : Text }; #Err : { #a; #b } },
      );
    y : shared query nested_records -> async ((nested_records, my_variant));
    f : t;
    g : shared list -> async (B, tree, stream);
    /// Doc comment for imported bbbbb service method
    bbbbb : shared b -> async ();
  }
}
