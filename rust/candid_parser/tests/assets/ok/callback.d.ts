import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';
import type { IDL } from '@dfinity/candid';

export interface CallbacksAreFun {
  'inline_callback' : [Principal, string],
  'callback' : Fn,
}
export type Fn = ActorMethod<[bigint], bigint>;

