import type { Principal } from '@dfinity/principal';
export type List = [] | [{ 'head' : bigint, 'tail' : List }];
export interface broker { 'find' : (arg_0: string) => Promise<Principal> }
export type f = (arg_0: List, arg_1: [Principal, string]) => Promise<
    [] | [List]
  >;
export type my_type = Principal;
export interface nested {
  _0_ : bigint,
  _1_ : bigint,
  _2_ : [bigint, bigint],
  _3_ : { _0_ : bigint, _42_ : bigint, _43_ : number },
  _40_ : bigint,
  _41_ : { _42_ : null } |
    { 'A' : null } |
    { 'B' : null } |
    { 'C' : null },
  _42_ : bigint,
}
export interface _SERVICE {
  'f' : (arg_0: Array<number>, arg_1: [] | [boolean]) => Promise<undefined>,
  'g' : (
      arg_0: my_type,
      arg_1: List,
      arg_2: [] | [List],
      arg_3: nested,
    ) => Promise<[bigint, Principal]>,
  'h' : (
      arg_0: Array<[] | [string]>,
      arg_1: { 'A' : bigint } |
        { 'B' : [] | [string] },
      arg_2: [] | [List],
    ) => Promise<{ _42_ : {}, 'id' : bigint }>,
  'i' : f,
}
