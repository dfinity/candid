import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';
import type { IDL } from '@dfinity/candid';

export type f = ActorMethod<[number], number>;
export type foo = [] | [string | undefined];
export type g = f;
export type h = ActorMethod<[[Principal, string]], [Principal, string]>;
export type o = Array<o>;
export interface _SERVICE {
  'f' : ActorMethod<[bigint], [Principal, string]>,
  'foo' : ActorMethod<[], foo>,
  'g' : f,
  'h' : g,
  'o' : ActorMethod<[o], o>,
}
export declare const idlFactory: IDL.InterfaceFactory;
export declare const init: (args: { IDL: typeof IDL }) => IDL.Type[];
