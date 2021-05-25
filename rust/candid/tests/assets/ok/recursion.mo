type A = B;
type B = ?A;
type list = ?node;
type node = { 'head'  : Nat; 'tail'  : list };
type s = actor { 'f' : t; 'g' : shared list -> async (B, tree, stream) };
type stream = ?{ 'head'  : Nat; 'next'  : shared query () -> async stream };
type t = shared s -> async ();
type tree = {
  #'branch'  : { 'val'  : Int; 'left'  : tree; 'right'  : tree };
  #'leaf'  : Int;
};
public type _MAIN = s
