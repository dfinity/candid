import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';
import type { IDL } from '@dfinity/candid';

export type Func = ActorMethod<[], Service>;
export interface Service { 'f' : Func }
export type Service2 = Service;
export interface _SERVICE {
  'asArray' : ActorMethod<[], [Array<Service2>, Array<Func>]>,
  'asPrincipal' : ActorMethod<[], [Service2, Func]>,
  'asRecord' : ActorMethod<[], [Service2, [] | [Service], Func]>,
  'asVariant' : ActorMethod<
    [],
    { 'a' : Service2 } |
      { 'b' : { 'f' : [] | [Func] } }
  >,
}
export declare const idlFactory: IDL.InterfaceFactory;
export declare const init: (args: { IDL: typeof IDL }) => IDL.Type[];
