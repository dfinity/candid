import { Principal } from '@dfinity/agent';
import BigNumber from 'bignumber.js';
export type f = (
    arg_0: number,
  ) => Promise<number>;
export type g = f;
export type h = (arg_0: f) => Promise<f>;
export type o = [] | [o];
export interface SERVICE {
  'f' : (arg_0: BigNumber) => Promise<h>,
  'g' : f,
  'h' : g,
  'o' : (arg_0: o) => Promise<o>,
};
