import { Principal } from '@dfinity/agent';
import BigNumber from 'bignumber.js';
export type A = B;
export type B = [] | [A];
export type list = [] | [node];
export type node = { 'head' : BigNumber, 'tail' : list };
export type s = { 'f' : t, 'g' : (arg_0: list) => Promise<[list]> };
export type stream = [] | [
  { 'head' : BigNumber, 'next' : () => Promise<stream> }
];
export type t = (arg_0: s) => Promise<undefined>;
export type tree = {
    'branch' : { 'val' : BigNumber, 'left' : tree, 'right' : tree }
  } |
  { 'leaf' : BigNumber };
export type SERVICE = s;
