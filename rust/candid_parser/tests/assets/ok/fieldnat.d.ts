import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';
import type { IDL } from '@dfinity/candid';

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
export declare const idlFactory: IDL.InterfaceFactory;
export declare const init: (args: { IDL: typeof IDL }) => IDL.Type[];
