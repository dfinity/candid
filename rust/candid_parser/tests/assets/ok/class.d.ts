import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';

export type List = [] | [[bigint, List]];
export interface _SERVICE {
  'get' : ActorMethod<[], List>,
  'set' : ActorMethod<[List], List>,
}
