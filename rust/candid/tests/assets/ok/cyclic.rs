// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.

type A = Option<B>
type B = Option<C>
type C = A
type X = Y
type Y = Z
type Z = A

