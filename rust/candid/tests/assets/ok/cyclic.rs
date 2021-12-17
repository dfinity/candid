// This is an experimental feature to generate Rust binding from Candid.
// You may want to manually adjust some of the types.

type A = Option<Box<B>>;
#[derive(CandidType, Deserialize)]
struct B(Option<Box<C>>)

#[derive(CandidType, Deserialize)]
struct C(A)

type X = Box<Y>;
#[derive(CandidType, Deserialize)]
struct Y(Box<Z>)

#[derive(CandidType, Deserialize)]
struct Z(A)

pub trait SERVICE {
  pub fn f(arg0: A, arg1: B, arg2: C, arg3: X, arg4: Y, arg5: Z) -> ();
}
