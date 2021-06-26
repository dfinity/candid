import type { Principal } from '@dfinity/principal';
export type if_ = {
    'branch' : { 'val' : bigint, 'left' : if_, 'right' : if_ }
  } |
  { 'leaf' : bigint };
export type list = [] | [node];
export interface node { 'head' : bigint, 'tail' : list };
export type o = [] | [o];
export interface return_ {
  'f' : t,
  'g' : (arg_0: list) => Promise<[if_, stream]>,
};
export type stream = [] | [{ 'head' : bigint, 'next' : [Principal, string] }];
export type t = (arg_0: Principal) => Promise<undefined>;
export default interface _SERVICE {
  'Oneway' : () => Promise<undefined>,
  'f_' : (arg_0: o) => Promise<o>,
  'field' : (arg_0: { 'test' : number, _1291438163_ : number }) => Promise<{}>,
  'fieldnat' : (arg_0: { _2_ : bigint, '2' : bigint }) => Promise<[bigint]>,
  'oneway' : (arg_0: number) => Promise<undefined>,
  'oneway_' : (arg_0: number) => Promise<undefined>,
  'query' : (arg_0: Array<number>) => Promise<Array<number>>,
  'return' : (arg_0: o) => Promise<o>,
  'service' : t,
  'tuple' : (arg_0: [bigint, Array<number>, string]) => Promise<
      [bigint, number]
    >,
  'variant' : (
      arg_0: { 'A' : null } |
        { 'B' : null } |
        { 'C' : null } |
        { 'D' : number },
    ) => Promise<undefined>,
};
