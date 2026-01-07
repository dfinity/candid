import type { Principal } from '@icp-sdk/core/principal';
import type { ActorMethod } from '@icp-sdk/core/agent';
import type { IDL } from '@icp-sdk/core/candid';

export type T = [T];
export interface _SERVICE {
  'f' : ActorMethod<[{}], never>,
  'g' : ActorMethod<[T], { 'a' : T }>,
  'h' : ActorMethod<[[T, never]], { 'a' : T } | { 'b' : {} }>,
}
export declare const idlFactory: IDL.InterfaceFactory;
export declare const init: (args: { IDL: typeof IDL }) => IDL.Type[];
