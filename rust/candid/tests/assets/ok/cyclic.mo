// This is a generated Motoko binding. Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.

type A = ?B;
type B = ?C;
type C = A;
type X = Y;
type Y = Z;
type Z = A;
type _SERVICE = actor { f : shared (A, B, C, X, Y, Z) -> async () }
