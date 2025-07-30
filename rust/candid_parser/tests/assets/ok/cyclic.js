import { IDL } from '@dfinity/candid';

export const A = IDL.Rec();
export const C = A;
export const B = IDL.Opt(C);
A.fill(IDL.Opt(B));
export const Z = A;
export const Y = Z;
export const X = Y;

export const idlService = IDL.Service({
  'f' : IDL.Func([A, B, C, X, Y, Z], [], []),
});

export const idlInitArgs = [];

/**
 * @deprecated Import IDL types directly from this module instead of using this factory function.
 */
export const idlFactory = ({ IDL }) => {
  const A = IDL.Rec();
  const C = A;
  const B = IDL.Opt(C);
  A.fill(IDL.Opt(B));
  const Z = A;
  const Y = Z;
  const X = Y;
  return IDL.Service({ 'f' : IDL.Func([A, B, C, X, Y, Z], [], []) });
};

/**
 * @deprecated Import IDL types directly from this module instead of using this factory function.
 */
export const init = ({ IDL }) => { return []; };
