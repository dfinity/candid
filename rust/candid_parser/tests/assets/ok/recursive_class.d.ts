import type { Principal } from '@dfinity/principal';
import type { ActorMethod } from '@dfinity/agent';

export interface s { 'next' : ActorMethod<[], Principal> }
export interface _SERVICE extends s {}
