import type { ActorMethod } from '@dfinity/agent';
import type { IDL } from '@dfinity/candid';
import type { Principal } from '@dfinity/principal';

export type A = [] | [B];
export type B = [] | [C];
export type C = A;
export type X = Y;
export type Y = Z;
export type Z = A;
export interface _SERVICE { 'f' : ActorMethod<[A, B, C, X, Y, Z], undefined> }
export declare const idlService: IDL.ServiceClass;
export declare const idlInitArgs: IDL.Type[];
export declare const idlFactory: IDL.InterfaceFactory;
export declare const init: (args: { IDL: typeof IDL }) => IDL.Type[];
