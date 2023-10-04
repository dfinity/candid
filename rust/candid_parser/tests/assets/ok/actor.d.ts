import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';

export type f = ActorMethod<[number], number>;
export type g = f;
export type h = ActorMethod<[[Principal, string]], [Principal, string]>;
export type o = [] | [o];
export interface _SERVICE {
  'f' : ActorMethod<[bigint], [Principal, string]>,
  'g' : f,
  'h' : g,
  'o' : ActorMethod<[o], o>,
}
