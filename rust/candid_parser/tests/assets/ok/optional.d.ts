import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';
import type { IDL } from '@dfinity/candid';

export type nested = [] | [[] | [bigint]];
export type option1 = [] | [bigint];
export type option2 = [] | [option1];
export type option3 = [] | [option2];
export interface _SERVICE { 'f' : ActorMethod<[], [option1, option2]> }
export declare const idlFactory: IDL.InterfaceFactory;
export declare const init: (args: { IDL: typeof IDL }) => IDL.Type[];
