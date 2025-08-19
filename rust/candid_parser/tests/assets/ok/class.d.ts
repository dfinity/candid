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
export declare const idlFactory: IDL.InterfaceFactory;
export declare const init: (args: { IDL: typeof IDL }) => IDL.Type[];
