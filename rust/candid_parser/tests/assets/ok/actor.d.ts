import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';
import type { IDL } from '@dfinity/candid';

export type doubleNestedOpt = [] | [[] | [string | undefined]];
export type f = ActorMethod<[number], number>;
export type g = f;
export type h = ActorMethod<[[Principal, string]], [Principal, string]>;
export type nestedOpt = [] | [string | undefined];
export type normalOpt = string | undefined;
export type recursiveOpt = [] | [recursiveOpt];
export interface _SERVICE {
  'doubleNestedOpt' : ActorMethod<[doubleNestedOpt], doubleNestedOpt>,
  'f' : ActorMethod<[bigint], [Principal, string]>,
  'g' : f,
  'h' : g,
  'nestedOpt' : ActorMethod<[nestedOpt], nestedOpt>,
  'normalOpt' : ActorMethod<[normalOpt], normalOpt>,
  'recursiveOpt' : ActorMethod<[recursiveOpt], recursiveOpt>,
}
export declare const idlFactory: IDL.InterfaceFactory;
export declare const init: (args: { IDL: typeof IDL }) => IDL.Type[];
