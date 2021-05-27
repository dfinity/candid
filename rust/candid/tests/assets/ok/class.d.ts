import type { Principal } from '@dfinity/agent';
export type List = [] | [[bigint, List]];
export default interface _SERVICE {
  'get' : () => Promise<List>,
  'set' : (arg_0: List) => Promise<List>,
};
