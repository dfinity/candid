export default ({ IDL }) => {
  const A = IDL.Rec();
  const C = A;
  const B = IDL.Opt(C);
  A.fill(IDL.Opt(B));
  const Z = A;
  const Y = Z;
  const X = Y;
  return IDL.Service({ 'f' : IDL.Func([A, B, C, X, Y, Z], [], []) });
}
