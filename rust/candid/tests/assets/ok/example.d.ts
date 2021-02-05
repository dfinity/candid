import { Principal } from '@dfinity/agent';
import BigNumber from 'bignumber.js';
export type List = [] | [
  { 'head' : BigNumber, 'tail' : List }
];
export type broker = {
  'find' : (arg_0: string) => Promise<
      { 'current' : () => Promise<number>, 'up' : () => Promise<undefined> }
    >,
};
export type f = (
    arg_0: List,
    arg_1: (arg_0: number) => Promise<BigNumber>,
  ) => Promise<[] | [List]>;
export type my_type = Principal;
export type nested = {
  _0_ : BigNumber,
  _1_ : BigNumber,
  _2_ : [BigNumber, BigNumber],
  _3_ : { _0_ : BigNumber, _42_ : BigNumber, _43_ : number },
  _40_ : BigNumber,
  _41_ : { _42_ : null } |
    { 'A' : null } |
    { 'B' : null } |
    { 'C' : null },
  _42_ : BigNumber,
};
export interface SERVICE {
  'f' : (arg_0: Array<number>, arg_1: [] | [boolean]) => Promise<undefined>,
  'g' : (
      arg_0: my_type,
      arg_1: List,
      arg_2: [] | [List],
      arg_3: nested,
    ) => Promise<[my_type, List, [] | [List], nested]>,
  'h' : (
      arg_0: Array<[] | [string]>,
      arg_1: { 'A' : BigNumber } |
        { 'B' : [] | [string] },
      arg_2: [] | [List],
    ) => Promise<{ _42_ : {}, 'id' : BigNumber }>,
  'i' : f,
};
