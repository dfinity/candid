import type { Principal } from '@dfinity/agent';
export type List = [] | [
  { 'head' : BigInt, 'tail' : List }
];
export interface broker { 'find' : (arg_0: string) => Promise<Principal> };
export type f = (arg_0: List, arg_1: [Principal, string]) => Promise<
    [] | [List]
  >;
export type my_type = Principal;
export interface nested {
  _0_ : BigInt,
  _1_ : BigInt,
  _2_ : [BigInt, BigInt],
  _3_ : { _0_ : BigInt, _42_ : BigInt, _43_ : number },
  _40_ : BigInt,
  _41_ : { _42_ : null } |
    { 'A' : null } |
    { 'B' : null } |
    { 'C' : null },
  _42_ : BigInt,
};
export default interface _SERVICE {
  'f' : (arg_0: Array<number>, arg_1: [] | [boolean]) => Promise<undefined>,
  'g' : (
      arg_0: my_type,
      arg_1: List,
      arg_2: [] | [List],
      arg_3: nested,
    ) => Promise<[BigInt, Principal]>,
  'h' : (
      arg_0: Array<[] | [string]>,
      arg_1: { 'A' : BigInt } |
        { 'B' : [] | [string] },
      arg_2: [] | [List],
    ) => Promise<{ _42_ : {}, 'id' : BigInt }>,
  'i' : f,
};
