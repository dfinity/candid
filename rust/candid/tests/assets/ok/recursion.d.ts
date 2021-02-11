import type { Principal } from '@dfinity/agent';
import type BigNumber from 'bignumber.js';
export type A = B;
export type B = [] | [A];
export type list = [] | [node];
export interface node { 'head' : BigNumber, 'tail' : list };
export interface s {
  'f' : t,
  'g' : (arg_0: list) => Promise<[B, tree, stream]>,
};
export type stream = [] | [
  { 'head' : BigNumber, 'next' : [Principal, string] }
];
export type t = (arg_0: Principal) => Promise<undefined>;
export type tree = {
    'branch' : { 'val' : BigNumber, 'left' : tree, 'right' : tree }
  } |
  { 'leaf' : BigNumber };
export default s;
