import type { Principal } from '@dfinity/agent';
import type BigNumber from 'bignumber.js';
export type List = [] | [
  [BigNumber, List]
];
export default interface _SERVICE {
  'get' : () => Promise<List>,
  'set' : (arg_0: List) => Promise<List>,
};
