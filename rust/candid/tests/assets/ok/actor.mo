type f = shared Int8 -> async Int8;
type g = f;
type h = shared f -> async f;
type o = ?o;
public type _MAIN = {
  'f' : shared Nat -> async h;
  'g' : f;
  'h' : g;
  'o' : shared o -> async o;
}
