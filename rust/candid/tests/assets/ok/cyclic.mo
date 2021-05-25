type A = ?B;
type B = ?C;
type C = A;
type X = Y;
type Y = Z;
type Z = A;
public type _MAIN = { f : shared (A, B, C, X, Y, Z) -> async () }
