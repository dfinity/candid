type A = {
  '\u{e000}'  : Nat;
  '📦🍦'  : Nat;
  '字段名'  : Nat;
  '字 段 名2'  : Nat;
};
type B = { #'' ; #'空的' ; #'  空的  ' ; #'1⃣️2⃣️3⃣️'  };
public type _MAIN = {
  '' : shared Nat -> async Nat;
  '✈️  🚗 ⛱️ ' : shared () -> ();
  '函数名' : shared A -> async B;
  '👀' : shared query Nat -> async Nat;
}
