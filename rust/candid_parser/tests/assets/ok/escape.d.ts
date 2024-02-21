import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';
import type { IDL } from '@dfinity/candid';

export interface t {
  '\"' : bigint,
  '\'' : bigint,
  '\"\'' : bigint,
  '\\\n\'\"' : bigint,
}
export interface _SERVICE { '\n\'\"\'\'\"\"\r\t' : ActorMethod<[t], undefined> }
export declare const idlFactory: IDL.InterfaceFactory;
export declare const init: (args: { IDL: typeof IDL }) => IDL.Type[];
