import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';
import type { IDL } from '@dfinity/candid';

export type List = [] | [[bigint, List]];
export interface _SERVICE {
  'get' : ActorMethod<[], List>,
  'set' : ActorMethod<[List], List>,
}
export declare const idlFactory: IDL.InterfaceFactory;
