import type { ActorMethod } from '@dfinity/agent';
import type { IDL } from '@dfinity/candid';
import type { Principal } from '@dfinity/principal';

export type T = [T];
export interface _SERVICE {
  'f' : ActorMethod<[{}], never>,
  'g' : ActorMethod<[T], { 'a' : T }>,
  'h' : ActorMethod<[[T, never]], { 'a' : T } | { 'b' : {} }>,
}
export declare const idlService: IDL.ServiceClass;
export declare const idlInitArgs: IDL.Type[];
export declare const idlFactory: IDL.InterfaceFactory;
export declare const init: (args: { IDL: typeof IDL }) => IDL.Type[];
