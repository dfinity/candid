import type { Principal } from '@icp-sdk/core/principal';
import type { ActorMethod } from '@icp-sdk/core/agent';
import type { IDL } from '@icp-sdk/core/candid';

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
export declare const idlFactory: IDL.InterfaceFactory;
export declare const init: (args: { IDL: typeof IDL }) => IDL.Type[];
