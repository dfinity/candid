import type { Principal } from '@dfinity/agent';
import type BigNumber from 'bignumber.js';
export interface t {
  '\"' : BigNumber,
  '\'' : BigNumber,
  '\"\'' : BigNumber,
  '\\\n\'\"' : BigNumber,
};
export default interface {
  '\n\'\"\'\'\"\"\r\t' : (arg_0: t) => Promise<undefined>,
};
