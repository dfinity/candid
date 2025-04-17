import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';
import type { IDL } from '@dfinity/candid';

export type if_ = {
    'branch' : { 'val' : bigint, 'left' : if_, 'right' : if_ }
  } |
  { 'leaf' : bigint };
export type list = [] | [node];
export interface node { 'head' : bigint, 'tail' : list }
export type o = [] | [o];
export interface return_ { 'f' : t, 'g' : ActorMethod<[list], [if_, stream]> }
export type stream = [] | [{ 'head' : bigint, 'next' : [Principal, string] }];
export type t = ActorMethod<[Principal], undefined>;
export interface _SERVICE {
  'Oneway' : ActorMethod<[], undefined>,
  'f_' : ActorMethod<[o], o>,
  'field' : ActorMethod<[{ 'test' : number, _1291438163_ : number }], {}>,
  'fieldnat' : ActorMethod<[{ _2_ : bigint, '2' : bigint }], [bigint]>,
  'oneway' : ActorMethod<[number], undefined>,
  'oneway_' : ActorMethod<[number], undefined>,
  'query' : ActorMethod<[Uint8Array | number[]], Uint8Array | number[]>,
  'return' : ActorMethod<[o], o>,
  'service' : t,
  'tuple' : ActorMethod<
    [[bigint, Uint8Array | number[], string]],
    [bigint, number]
  >,
  'variant' : ActorMethod<
    [{ 'A' : null } | { 'B' : null } | { 'C' : null } | { 'D' : number }],
    undefined
  >,
}
export declare const idlFactory: IDL.InterfaceFactory;
export declare const init: (args: { IDL: typeof IDL }) => IDL.Type[];
