import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';

export interface t {
  '\"' : bigint,
  '\'' : bigint,
  '\"\'' : bigint,
  '\\\n\'\"' : bigint,
}
export interface _SERVICE { '\n\'\"\'\'\"\"\r\t' : ActorMethod<[t], undefined> }
