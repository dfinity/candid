// This is a generated Motoko binding.
// Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.

module {
  public type A = B;
  public type B = ?A;
  public type node = { head : Nat; tail : list };
  public type list = ?node;
  public type tree = {
    #branch : { val : Int; left : tree; right : tree };
    #leaf : Int;
  };
  public type s = actor { f : t; g : shared list -> async (B, tree, stream) };
  public type t = shared (server : s) -> async ();
  public type stream = ?{ head : Nat; next : shared query () -> async stream };
  /// Doc comment for b in imported file
  public type b = (Int, Nat);
  /// Doc comment for a in imported file
  public type a = { #a; #b : b };
  /// Doc comment for prim type
  public type my_type = Principal;
  /// Doc comment for List
  public type List = ?{ head : Int; tail : List };
  public type f = shared (List, shared Int32 -> async Int64) -> async (
      ?List,
      res,
    );
  /// Doc comment for broker service
  public type broker = actor {
    find : shared (name : Text) -> async actor {
        current : shared () -> async Nat32;
        up : shared () -> async ();
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
  public type nested_res = {
    #Ok : { #Ok; #Err };
    #Err : {
      /// Doc comment for Ok in nested variant
      #Ok : { content : Text };
      /// Doc comment for Err in nested variant
      #Err : { _0_  : Int };
    };
  };
  /// Doc comment for service
  public type Self = actor {
    /// Doc comment for bbbbb method in imported service
    bbbbb : shared b -> async ();
    f : t;
    /// Doc comment for f1 method of service
    f1 : shared (list, test : Blob, ?Bool) -> ();
    g : shared list -> async (B, tree, stream);
    g1 : shared query (my_type, List, ?List, nested) -> async (
        Int,
        broker,
        nested_res,
      );
    h : shared ([?Text], { #A : Nat; #B : ?Text }, ?List) -> async {
        /// Doc comment for 0x2a field in h method return
        _42_  : {};
        /// Doc comment for id field in h method return
        id : Nat;
      };
    /// Doc comment for i method of service
    i : f;
    x : shared composite query (a, b) -> async (
        ?a,
        ?b,
        { #Ok : { result : Text }; #Err : { #a; #b } },
      );
  }
}
