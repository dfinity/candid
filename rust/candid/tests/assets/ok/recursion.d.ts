import type { Principal } from '@dfinity/principal';
export type A = B;
export type B = [] | [A];
export type list = [] | [node];
export interface node { 'head' : bigint, 'tail' : list };
export interface s {
  'f' : t,
  'g' : (arg_0: list) => Promise<[B, tree, stream]>,
};
export type stream = [] | [{ 'head' : bigint, 'next' : [Principal, string] }];
export type t = (arg_0: Principal) => Promise<undefined>;
export type tree = {
    'branch' : { 'val' : bigint, 'left' : tree, 'right' : tree }
  } |
  { 'leaf' : bigint };
export default s;
