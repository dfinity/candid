import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';
import type { IDL } from '@dfinity/candid';

/**
 * *\/ import { malicious } from 'attacker'; console.log('injected!'); /*
 * Normal doc line
 * Another *\/ attempt /* to inject
 */
export interface MaliciousType {
  /**
   * Doc comment for field with *\/ malicious code /* in it
   */
  'field' : string,
}
/**
 * Service with *\/ malicious *\/ doc
 */
export interface _SERVICE {
  /**
   * Method with *\/ in doc comment
   */
  'get' : ActorMethod<[], MaliciousType>,
}
export declare const idlFactory: IDL.InterfaceFactory;
export declare const init: (args: { IDL: typeof IDL }) => IDL.Type[];
