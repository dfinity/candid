import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';
import type { IDL } from '@dfinity/candid';

export type a = { 'a' : null } |
  { 'b' : b };
export type b = [bigint, bigint];
export type id = number;

