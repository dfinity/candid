import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';

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
