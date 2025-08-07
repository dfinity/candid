import type { ActorMethod } from '@dfinity/agent';
import type { IDL } from '@dfinity/candid';
import type { Principal } from '@dfinity/principal';

export interface A {
  '\u{e000}' : bigint,
  '📦🍦' : bigint,
  '字段名' : bigint,
  '字 段 名2' : bigint,
}
export type B = { '' : null } |
  { '空的' : null } |
  { '  空的  ' : null } |
  { '1⃣️2⃣️3⃣️' : null };
export interface _SERVICE {
  '' : ActorMethod<[bigint], bigint>,
  '✈️  🚗 ⛱️ ' : ActorMethod<[], undefined>,
  '函数名' : ActorMethod<[A], B>,
  '👀' : ActorMethod<[bigint], bigint>,
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
