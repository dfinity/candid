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
/**
 * @deprecated Since `@dfinity/candid` v3.2.1, you can import IDL types directly from this module instead of using this factory function.
 */
export declare const idlFactory: IDL.InterfaceFactory;
/**
 * @deprecated Since `@dfinity/candid` v3.2.1, you can import IDL types directly from this module instead of using this factory function.
 */
export declare const init: (args: { IDL: typeof IDL }) => IDL.Type[];
