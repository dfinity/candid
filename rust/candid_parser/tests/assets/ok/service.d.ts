import type { ActorMethod } from '@dfinity/agent';
import type { IDL } from '@dfinity/candid';
import type { Principal } from '@dfinity/principal';

export type Func = ActorMethod<[], Principal>;
export interface Service { 'f' : Func }
export type Service2 = Service;
export interface _SERVICE {
  'asArray' : ActorMethod<[], [Array<Principal>, Array<[Principal, string]>]>,
  'asPrincipal' : ActorMethod<[], [Principal, [Principal, string]]>,
  'asRecord' : ActorMethod<
    [],
    [Principal, [] | [Principal], [Principal, string]]
  >,
  'asVariant' : ActorMethod<
    [],
    { 'a' : Principal } |
      { 'b' : { 'f' : [] | [[Principal, string]] } }
  >,
}
export declare const idlService: IDL.ServiceClass;
export declare const idlInitArgs: IDL.Type[];
export declare const idlFactory: IDL.InterfaceFactory;
export declare const init: (args: { IDL: typeof IDL }) => IDL.Type[];
