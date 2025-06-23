import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';
import type { IDL } from '@dfinity/candid';

export type doubleNested_opt = [] | [[] | [string | undefined]];
export type nested_opt = [] | [string | undefined];
export type normal_opt = string | undefined;
export type recursive_opt = [] | [recursive_opt];
export interface _SERVICE {
  'doubleNested_opt' : ActorMethod<[doubleNested_opt], doubleNested_opt>,
  'nested_opt' : ActorMethod<[nested_opt], nested_opt>,
  'normal_opt' : ActorMethod<[normal_opt], normal_opt>,
  'recursive_opt' : ActorMethod<[recursive_opt], recursive_opt>,
}
export declare const idlFactory: IDL.InterfaceFactory;
export declare const init: (args: { IDL: typeof IDL }) => IDL.Type[];
