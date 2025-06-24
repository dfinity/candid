import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';
import type { IDL } from '@dfinity/candid';

export type f = ActorMethod<[number], number>;
export type g = f;
export type h = ActorMethod<[[Principal, string]], [Principal, string]>;
export type o = [] | [o];
export interface _SERVICE {
  'f' : ActorMethod<[bigint], [Principal, string]>,
  'g' : f,
  'h' : g,
  'h2' : h,
  'o' : ActorMethod<[o], o>,
}
export declare const idlFactory: IDL.InterfaceFactory;
export declare const init: (args: { IDL: typeof IDL }) => IDL.Type[];
