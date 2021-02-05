import { Principal } from '@dfinity/agent';
import BigNumber from 'bignumber.js';
export type List = [] | [
  [BigNumber, List]
];
export interface SERVICE {
  'get' : () => Promise<List>,
  'set' : (arg_0: List) => Promise<List>,
};
