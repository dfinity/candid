import type { ActorMethod } from '@dfinity/agent';
import type { IDL } from '@dfinity/candid';
import type { Principal } from '@dfinity/principal';

export type List = [] | [[bigint, List]];
export interface Profile { 'age' : number, 'name' : string }
/**
 * Doc comment for class service
 */
export interface _SERVICE {
  /**
   * Doc comment for get method in class service
   */
  'get' : ActorMethod<[], List>,
  'set' : ActorMethod<[List], List>,
}
export declare const idlService: IDL.ServiceClass;
export declare const idlInitArgs: IDL.Type[];
/**
 * @deprecated Since `@dfinity/candid` v3.2.1, you can import IDL types directly from this module instead of using this factory function.
 */
export declare const idlFactory: IDL.InterfaceFactory;
/**
 * @deprecated Since `@dfinity/candid` v3.2.1, you can import IDL types directly from this module instead of using this factory function.
 */
export declare const init: (args: { IDL: typeof IDL }) => IDL.Type[];
