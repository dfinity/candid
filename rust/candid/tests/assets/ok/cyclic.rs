// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.

type A = Option<B>
type B = Option<C>
type C = A
type X = Y
type Y = Z
type Z = A
pub trait SERVICE {
  pub fn f(arg0: A, arg1: B, arg2: C, arg3: X, arg4: Y, arg5: Z) -> ();
}
