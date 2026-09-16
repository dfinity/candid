import type { Principal } from '@icp-sdk/core/principal';
import type { ActorMethod } from '@icp-sdk/core/agent';
import type { IDL } from '@icp-sdk/core/candid';

/**
 * The method names of a service type are arbitrary Candid text values, but every binding emits
 * them into a string literal of the target language. Names containing quotes, backslashes, comment
 * markers or newlines have to be escaped for the generated code to stay well-formed.
 */
export type f = ActorMethod<[], undefined>;
export interface inner {
  'backslash\\' : f,
  'braces { } and parens ( )' : f,
  'comment markers // and /* */' : f,
  'newline\nand carriage return\r' : f,
  'quote\"' : f,
  'tab\tand semicolon;' : f,
}
export interface _SERVICE {
  'ping' : ActorMethod<[], string>,
  'use_inner' : ActorMethod<[Principal], undefined>,
}
export declare const idlFactory: IDL.InterfaceFactory;
export declare const init: (args: { IDL: typeof IDL }) => IDL.Type[];
