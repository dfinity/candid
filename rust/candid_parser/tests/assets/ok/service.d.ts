import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';
import type { IDL } from '@dfinity/candid';

export type Func = [Principal, string];
export interface Service { 'f' : ActorMethod<[], Principal> }
export type Service2 = Service;
export interface _SERVICE {
  'asArray' : ActorMethod<[], [Array<Principal>, Array<Func>]>,
  'asPrincipal' : ActorMethod<[], [Principal, Func]>,
  'asRecord' : ActorMethod<[], [Principal, [] | [Principal], Func]>,
  'asVariant' : ActorMethod<
    [],
    { 'a' : Principal } |
      { 'b' : { 'f' : [] | [Func] } }
  >,
}
export declare const idlFactory: IDL.InterfaceFactory;
export declare const init: (args: { IDL: typeof IDL }) => IDL.Type[];
