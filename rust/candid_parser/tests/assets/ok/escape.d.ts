import type { ActorMethod } from '@dfinity/agent';
import type { IDL } from '@dfinity/candid';
import type { Principal } from '@dfinity/principal';

export interface t {
  '\"' : bigint,
  '\'' : bigint,
  '\"\'' : bigint,
  '\\\n\'\"' : bigint,
}
export interface _SERVICE { '\n\'\"\'\'\"\"\r\t' : ActorMethod<[t], undefined> }
export declare const idlService: IDL.ServiceClass;
export declare const idlInitArgs: IDL.Type[];
export declare const idlFactory: IDL.InterfaceFactory;
export declare const init: (args: { IDL: typeof IDL }) => IDL.Type[];
