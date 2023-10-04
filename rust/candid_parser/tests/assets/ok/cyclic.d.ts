import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';

export type A = [] | [B];
export type B = [] | [C];
export type C = A;
export type X = Y;
export type Y = Z;
export type Z = A;
export interface _SERVICE { 'f' : ActorMethod<[A, B, C, X, Y, Z], undefined> }
