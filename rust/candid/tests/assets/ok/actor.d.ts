import type { Principal } from '@dfinity/agent';
import type BigNumber from 'bignumber.js';
export type f = (
    arg_0: number,
  ) => Promise<number>;
export type g = f;
export type h = (arg_0: f) => Promise<f>;
export type o = [] | [o];
export default interface {
  'f' : (arg_0: BigNumber) => Promise<h>,
  'g' : f,
  'h' : g,
  'o' : (arg_0: o) => Promise<o>,
};
