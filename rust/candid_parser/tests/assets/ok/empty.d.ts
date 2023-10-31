import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';

export type T = [T];
export interface _SERVICE {
  'f' : ActorMethod<[{}], never>,
  'g' : ActorMethod<[T], { 'a' : T }>,
  'h' : ActorMethod<[[T, never]], { 'a' : T } | { 'b' : {} }>,
}
