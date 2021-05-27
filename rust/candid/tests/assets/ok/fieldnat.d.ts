import type { Principal } from '@dfinity/agent';
export interface non_tuple { _1_ : string, _2_ : string };
export type tuple = [string, string];
export default interface _SERVICE {
  'bab' : (arg_0: bigint, arg_1: bigint) => Promise<undefined>,
  'bar' : (arg_0: { '2' : bigint }) => Promise<undefined>,
  'bas' : (arg_0: [bigint, bigint]) => Promise<[string, bigint]>,
  'baz' : (arg_0: { _2_ : bigint, '2' : bigint }) => Promise<{}>,
  'bba' : (arg_0: tuple) => Promise<non_tuple>,
  'bib' : (arg_0: [bigint]) => Promise<{ _0_ : bigint }>,
  'foo' : (arg_0: { _2_ : bigint }) => Promise<{ _2_ : bigint, '_2' : bigint }>,
};
