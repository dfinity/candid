import { Principal } from '@dfinity/agent';
import BigNumber from 'bignumber.js';
export type A = {
  '\u{e000}' : BigNumber,
  '📦🍦' : BigNumber,
  '字段名' : BigNumber,
  '字 段 名2' : BigNumber,
};
export type B = { '' : null } |
  { '空的' : null } |
  { '  空的  ' : null } |
  { '1⃣️2⃣️3⃣️' : null };
export interface SERVICE {
  '' : (arg_0: BigNumber) => Promise<BigNumber>,
  '✈️  🚗 ⛱️ ' : () => Promise<undefined>,
  '函数名' : (arg_0: A) => Promise<B>,
  '👀' : (arg_0: BigNumber) => Promise<BigNumber>,
};
