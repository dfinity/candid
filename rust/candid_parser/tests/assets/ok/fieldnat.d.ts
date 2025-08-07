import type { ActorMethod } from '@dfinity/agent';
import type { IDL } from '@dfinity/candid';
import type { Principal } from '@dfinity/principal';

export interface non_tuple { _1_ : string, _2_ : string }
export type tuple = [string, string];
export interface _SERVICE {
  'bab' : ActorMethod<[bigint, bigint], undefined>,
  'bar' : ActorMethod<[{ '2' : bigint }], { 'e20' : null } | { 'e30' : null }>,
  'bas' : ActorMethod<[[bigint, bigint]], [string, bigint]>,
  'baz' : ActorMethod<[{ _2_ : bigint, '2' : bigint }], {}>,
  'bba' : ActorMethod<[tuple], non_tuple>,
  'bib' : ActorMethod<[[bigint]], { _0_ : bigint }>,
  'foo' : ActorMethod<[{ _2_ : bigint }], { _2_ : bigint, '_2' : bigint }>,
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
