import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';

export type A = B;
export type B = [] | [A];
export type List = [] | [{ 'head' : bigint, 'tail' : List }];
export type a = { 'a' : null } |
  { 'b' : b };
export type b = [bigint, bigint];
export interface broker { 'find' : ActorMethod<[string], Principal> }
export type f = ActorMethod<[List, [Principal, string]], [] | [List]>;
export type list = [] | [node];
export type my_type = Principal;
export interface nested {
  _0_ : bigint,
  _1_ : bigint,
  _2_ : [bigint, bigint],
  _3_ : { _0_ : bigint, _42_ : bigint, _43_ : number },
  _40_ : bigint,
  _41_ : { _42_ : null } |
    { 'A' : null } |
    { 'B' : null } |
    { 'C' : null },
  _42_ : bigint,
}
export interface node { 'head' : bigint, 'tail' : list }
export interface s { 'f' : t, 'g' : ActorMethod<[list], [B, tree, stream]> }
export type stream = [] | [{ 'head' : bigint, 'next' : [Principal, string] }];
export type t = ActorMethod<[Principal], undefined>;
export type tree = {
    'branch' : { 'val' : bigint, 'left' : tree, 'right' : tree }
  } |
  { 'leaf' : bigint };
export interface _SERVICE {
  'f' : ActorMethod<[list, Array<number>, [] | [boolean]], undefined>,
  'g' : ActorMethod<[my_type, List, [] | [List], nested], [bigint, Principal]>,
  'h' : ActorMethod<
    [
      Array<[] | [string]>,
      { 'A' : bigint } |
        { 'B' : [] | [string] },
      [] | [List],
    ],
    { _42_ : {}, 'id' : bigint },
  >,
  'i' : f,
  'x' : ActorMethod<[a, b], [[] | [a], [] | [b]]>,
}
