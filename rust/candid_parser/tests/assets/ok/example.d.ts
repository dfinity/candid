import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';
import type { IDL } from '@dfinity/candid';

export type A = B;
export type B = [] | [A];
/**
 * This is a type block comment
 */
export type List = [] | [
  {
    /**
     * This is a field block comment
     */
    'head' : bigint,
    /**
     * This is a field comment
     */
    'tail' : List,
  }
];
export type a = { 'a' : null } |
  { 'b' : b };
/**
 * This is a type comment
 */
export type b = [bigint, bigint];
/**
 * This is another type comment
 */
export interface broker {
  /**
   * This is a service method block comment
   */
  'find' : ActorMethod<[string], Principal>,
}
export type f = ActorMethod<[List, [Principal, string]], [[] | [List], res]>;
export type list = [] | [node];
/**
 * This is a type comment
 */
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
export type nested_res = {
    /**
     * This is a variant comment
     */
    'Ok' : { 'Ok' : null } |
      { 'Err' : null }
  } |
  {
    /**
     * This is another variant comment
     * that spans multiple lines for variants
     */
    'Err' : { 'Ok' : { 'content' : string } } |
      { 'Err' : [bigint] }
  };
export interface node { 'head' : bigint, 'tail' : list }
export type res = {
    /**
     * This is a block comment for variant Ok
     */
    'Ok' : [bigint, bigint]
  } |
  {
    /**
     * This comment is a block comment for variant Err
     */
    'Err' : { 'error' : string }
  };
export interface s { 'f' : t, 'g' : ActorMethod<[list], [B, tree, stream]> }
export type stream = [] | [{ 'head' : bigint, 'next' : [Principal, string] }];
export type t = ActorMethod<[Principal], undefined>;
export type tree = {
    'branch' : { 'val' : bigint, 'left' : tree, 'right' : tree }
  } |
  { 'leaf' : bigint };
/**
 * This is a service comment
 * that spans multiple lines for services
 */
export interface _SERVICE {
  /**
   * This is a method comment on an imported service
   */
  'bbbbb' : ActorMethod<[b], undefined>,
  'f' : t,
  'f1' : ActorMethod<[list, Uint8Array | number[], [] | [boolean]], undefined>,
  'g' : ActorMethod<[list], [B, tree, stream]>,
  /**
   * This is a method comment
   */
  'g1' : ActorMethod<
    [my_type, List, [] | [List], nested],
    [bigint, Principal, nested_res]
  >,
  /**
   * This is a block comment for a method
   */
  'h' : ActorMethod<
    [
      Array<[] | [string]>,
      { 'A' : bigint } |
        { 'B' : [] | [string] },
      [] | [List],
    ],
    { _42_ : {}, 'id' : bigint }
  >,
  /**
   * This is a block comment for a method
   * that spans multiple lines,
   * even with wrong indentation
   */
  'i' : f,
  /**
   * This is another method comment
   * that spans multiple lines for methods
   */
  'x' : ActorMethod<
    [a, b],
    [
      [] | [a],
      [] | [b],
      { 'Ok' : { 'result' : string } } |
        { 'Err' : { 'a' : null } | { 'b' : null } },
    ]
  >,
}
export declare const idlFactory: IDL.InterfaceFactory;
export declare const init: (args: { IDL: typeof IDL }) => IDL.Type[];
