import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';
import type { IDL } from '@dfinity/candid';

export type Fn = ActorMethod<[bigint], bigint>;
export interface R { 'x' : bigint, 'fn' : Fn }
export interface RInline { 'x' : bigint, 'fn' : [Principal, string] }
export interface _SERVICE {
  'add_two' : ActorMethod<[bigint], bigint>,
  'fn' : Fn,
  'high_order_fn_inline' : ActorMethod<[bigint, [Principal, string]], bigint>,
  'high_order_fn_via_record' : ActorMethod<[R], bigint>,
  'high_order_fn_via_record_inline' : ActorMethod<[RInline], bigint>,
  'inline_fn' : ActorMethod<[bigint], bigint>,
}
export declare const idlFactory: IDL.InterfaceFactory;
export declare const init: (args: { IDL: typeof IDL }) => IDL.Type[];
