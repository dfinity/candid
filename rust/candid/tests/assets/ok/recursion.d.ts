import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';

export type A = B;
export type B = [] | [A];
export type list = [] | [node];
export interface node { 'head' : bigint, 'tail' : list }
export interface s { 'f' : t, 'g' : ActorMethod<[list], [B, tree, stream]> }
export type stream = [] | [{ 'head' : bigint, 'next' : [Principal, string] }];
export type t = ActorMethod<[Principal], undefined>;
export type tree = {
    'branch' : { 'val' : bigint, 'left' : tree, 'right' : tree }
  } |
  { 'leaf' : bigint };
export interface _SERVICE extends s {}
