import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';
import type { IDL } from '@dfinity/candid';

export type Result = { 'ok' : bigint } |
  { 'err' : string };
export interface Tokens { 'e8s' : bigint }
export interface TransferArgs {
  'toPrincipal' : Principal,
  'amount' : Tokens,
  'toSubaccount' : [] | [Uint8Array | number[]],
}
export interface _SERVICE { 'transfer' : ActorMethod<[TransferArgs], Result> }
export declare const idlFactory: IDL.InterfaceFactory;
export declare const init: (args: { IDL: typeof IDL }) => IDL.Type[];
