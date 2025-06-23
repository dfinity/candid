import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';
import type { IDL } from '@dfinity/candid';

export type f = [Principal, string];
export type g = f;
export type h = [Principal, string];
export type o = [] | [o];
export interface _SERVICE {
  'f' : ActorMethod<[bigint], h>,
  'g' : ActorMethod<[number], number>,
  'h' : ActorMethod<[number], number>,
  'h2' : ActorMethod<[f], f>,
  'o' : ActorMethod<[o], o>,
}
export declare const idlFactory: IDL.InterfaceFactory;
export declare const init: (args: { IDL: typeof IDL }) => IDL.Type[];
