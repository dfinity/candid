import type { Principal } from '@icp-sdk/core/principal';
import type { ActorMethod } from '@icp-sdk/core/agent';
import type { IDL } from '@icp-sdk/core/candid';

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
export declare const idlFactory: IDL.InterfaceFactory;
export declare const init: (args: { IDL: typeof IDL }) => IDL.Type[];
