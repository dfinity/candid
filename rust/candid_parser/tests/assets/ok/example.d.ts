import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';
import type { IDL } from '@dfinity/candid';

export type A = B;
export type B = [] | [A];
export interface node { 'head' : bigint, 'tail' : list }
export type list = [] | [node];
export type tree = {
    'branch' : { 'val' : bigint, 'left' : tree, 'right' : tree }
  } |
  { 'leaf' : bigint };
export interface s { 'f' : t, 'g' : ActorMethod<[list], [B, tree, stream]> }
export type t = ActorMethod<[Principal], undefined>;
export type stream = [] | [{ 'head' : bigint, 'next' : [Principal, string] }];
/**
 * Doc comment for b in imported file
 */
export type b = [bigint, bigint];
/**
 * Doc comment for a in imported file
 */
export type a = { 'a' : null } |
  { 'b' : b };
/**
 * Doc comment for prim type
 */
export type my_type = Principal;
/**
 * Doc comment for List
 */
export type List = [] | [
  {
    /**
     * Doc comment for List head
     */
    'head' : bigint,
    /**
     * Doc comment for List tail
     */
    'tail' : List,
  }
];
export type f = ActorMethod<[List, [Principal, string]], [[] | [List], res]>;
/**
 * Doc comment for broker service
 */
export interface broker { 'find' : ActorMethod<[string], Principal> }
/**
 * Doc comment for nested type
 */
export interface nested {
  _0_ : bigint,
  _1_ : bigint,
  /**
   * Doc comment for nested record
   */
  _2_ : [bigint, bigint],
  _3_ : { _0_ : bigint, _42_ : bigint, _43_ : number },
  _40_ : bigint,
  _41_ : { _42_ : null } |
    { 'A' : null } |
    { 'B' : null } |
    { 'C' : null },
  _42_ : bigint,
}
export type res = {
    /**
     * Doc comment for Ok variant
     */
    'Ok' : [bigint, bigint]
  } |
  {
    /**
     * Doc comment for Err variant
     */
    'Err' : {
      /**
       * Doc comment for error field in Err variant,
       * on multiple lines
       */
      'error' : string,
    }
  };
export type nested_res = { 'Ok' : { 'Ok' : null } | { 'Err' : null } } |
  {
    'Err' : {
        /**
         * Doc comment for Ok in nested variant
         */
        'Ok' : { 'content' : string }
      } |
      {
        /**
         * Doc comment for Err in nested variant
         */
        'Err' : [bigint]
      }
  };
/**
 * Doc comment for nested_records
 */
export interface nested_records {
  /**
   * Doc comment for nested_records field nested
   */
  'nested' : [] | [
    {
      /**
       * Doc comment for nested_records field nested_field
       */
      'nested_field' : string,
    }
  ],
}
export type my_variant = {
    /**
     * Doc comment for my_variant field a
     */
    'a' : {
      /**
       * Doc comment for my_variant field a field b
       */
      'b' : string,
    }
  } |
  {
    /**
     * Doc comment for my_variant field c
     */
    'c' : [] | [
      {
        /**
         * Doc comment for my_variant field c field d
         */
        'd' : string,
      }
    ]
  };
/**
 * Doc comment for service
 */
export interface _SERVICE {
  /**
   * Doc comment for bbbbb method in imported service
   */
  'bbbbb' : ActorMethod<[b], undefined>,
  'f' : t,
  /**
   * Doc comment for f1 method of service
   */
  'f1' : ActorMethod<[list, Uint8Array | number[], [] | [boolean]], undefined>,
  'g' : ActorMethod<[list], [B, tree, stream]>,
  'g1' : ActorMethod<
    [my_type, List, [] | [List], nested],
    [bigint, Principal, nested_res]
  >,
  'h' : ActorMethod<
    [
      Array<[] | [string]>,
      { 'A' : bigint } |
        { 'B' : [] | [string] },
      [] | [List],
    ],
    {
      /**
       * Doc comment for 0x2a field in h method return
       */
      _42_ : {},
      /**
       * Doc comment for id field in h method return
       */
      'id' : bigint,
    }
  >,
  /**
   * Doc comment for i method of service
   */
  'i' : f,
  'x' : ActorMethod<
    [a, b],
    [
      [] | [a],
      [] | [b],
      { 'Ok' : { 'result' : string } } |
        { 'Err' : { 'a' : null } | { 'b' : null } },
    ]
  >,
  'y' : ActorMethod<[nested_records], [nested_records, my_variant]>,
}
export declare const idlFactory: IDL.InterfaceFactory;
export declare const init: (args: { IDL: typeof IDL }) => IDL.Type[];
