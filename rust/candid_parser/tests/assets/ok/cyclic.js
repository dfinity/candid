import { IDL } from '@dfinity/candid';

export const A = IDL.Rec();
export const C = A;
export const B = IDL.Opt(C);
A.fill(IDL.Opt(B));
export const Z = A;
export const Y = Z;
export const X = Y;

export const _ServiceTypes = {'f': IDL.Func([A, B, C, X, Y, Z], [], [])}

export const idlFactory = ({ IDL }) => {
  return IDL.Service({ 'f': _ServiceTypes['f'] });
};

export const init = ({ IDL }) => { return []; };
