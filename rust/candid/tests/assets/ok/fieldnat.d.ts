import type { Principal } from '@dfinity/agent';
import type BigNumber from 'bignumber.js';
export default interface {
  'bab' : (arg_0: BigNumber, arg_1: BigNumber) => Promise<undefined>,
  'bar' : (arg_0: { '2' : BigNumber }) => Promise<undefined>,
  'bas' : (arg_0: [BigNumber, BigNumber]) => Promise<[string, BigNumber]>,
  'baz' : (arg_0: { _2_ : BigNumber, '2' : BigNumber }) => Promise<{}>,
  'bib' : (arg_0: [BigNumber]) => Promise<{ _0_ : BigNumber }>,
  'foo' : (arg_0: { _2_ : BigNumber }) => Promise<
      { _2_ : BigNumber, '_2' : BigNumber }
    >,
};
