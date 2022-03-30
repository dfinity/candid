import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';

export interface non_tuple { _1_ : string, _2_ : string }
export type tuple = [string, string];
export interface _SERVICE {
  'bab' : ActorMethod<[bigint, bigint], undefined>,
  'bar' : ActorMethod<[{ '2' : bigint }], undefined>,
  'bas' : ActorMethod<[[bigint, bigint]], [string, bigint]>,
  'baz' : ActorMethod<[{ _2_ : bigint, '2' : bigint }], {}>,
  'bba' : ActorMethod<[tuple], non_tuple>,
  'bib' : ActorMethod<[[bigint]], { _0_ : bigint }>,
  'foo' : ActorMethod<[{ _2_ : bigint }], { _2_ : bigint, '_2' : bigint }>,
}
