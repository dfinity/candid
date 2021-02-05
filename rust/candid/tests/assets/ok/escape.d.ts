import { Principal } from '@dfinity/agent';
import BigNumber from 'bignumber.js';
export type t = {
  '\"' : BigNumber,
  '\'' : BigNumber,
  '\"\'' : BigNumber,
  '\\\n\'\"' : BigNumber,
};
export interface SERVICE {
  '\n\'\"\'\'\"\"\r\t' : (arg_0: t) => Promise<undefined>,
};
