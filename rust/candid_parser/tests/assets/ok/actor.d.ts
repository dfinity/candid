import type { ActorMethod } from '@dfinity/agent';
import type { IDL } from '@dfinity/candid';
import type { Principal } from '@dfinity/principal';

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
export declare const idlService: IDL.ServiceClass;
export declare const idlInitArgs: IDL.Type[];
/**
 * @deprecated Since `@dfinity/candid` v3.2.1, you can import IDL types directly from this module instead of using this factory function.
 */
export declare const idlFactory: IDL.InterfaceFactory;
/**
 * @deprecated Since `@dfinity/candid` v3.2.1, you can import IDL types directly from this module instead of using this factory function.
 */
export declare const init: (args: { IDL: typeof IDL }) => IDL.Type[];
