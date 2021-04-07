import type { Principal } from '@dfinity/agent';
export type A = B;
export type B = [] | [A];
export type list = [] | [node];
export interface node { 'head' : BigInt, 'tail' : list };
export interface s {
  'f' : t,
  'g' : (arg_0: list) => Promise<[B, tree, stream]>,
};
export type stream = [] | [{ 'head' : BigInt, 'next' : [Principal, string] }];
export type t = (arg_0: Principal) => Promise<undefined>;
export type tree = {
    'branch' : { 'val' : BigInt, 'left' : tree, 'right' : tree }
  } |
  { 'leaf' : BigInt };
export default s;
