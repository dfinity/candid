import type { Principal } from '@dfinity/agent';
import type BigNumber from 'bignumber.js';
export type A = [] | [
  B
];
export type B = [] | [C];
export type C = A;
export type X = Y;
export type Y = Z;
export type Z = A;
export default interface {
  'f' : (arg_0: A, arg_1: B, arg_2: C, arg_3: X, arg_4: Y, arg_5: Z) => Promise<
      undefined
    >,
};
