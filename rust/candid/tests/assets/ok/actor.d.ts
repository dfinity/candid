import type { Principal } from '@dfinity/agent';
export type f = (arg_0: number) => Promise<number>;
export type g = f;
export type h = (arg_0: [Principal, string]) => Promise<[Principal, string]>;
export type o = [] | [o];
export default interface _SERVICE {
  'f' : (arg_0: bigint) => Promise<[Principal, string]>,
  'g' : f,
  'h' : g,
  'o' : (arg_0: o) => Promise<o>,
};
