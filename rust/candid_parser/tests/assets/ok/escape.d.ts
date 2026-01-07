import type { Principal } from '@icp-sdk/core/principal';
import type { ActorMethod } from '@icp-sdk/core/agent';
import type { IDL } from '@icp-sdk/core/candid';

export interface t {
  '\"' : bigint,
  '\'' : bigint,
  '\"\'' : bigint,
  '\\\n\'\"' : bigint,
}
export interface _SERVICE { '\n\'\"\'\'\"\"\r\t' : ActorMethod<[t], undefined> }
export declare const idlFactory: IDL.InterfaceFactory;
export declare const init: (args: { IDL: typeof IDL }) => IDL.Type[];
