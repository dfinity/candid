import { type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
import type { Principal } from "@dfinity/principal";
import { CreateActorOptions } from "declarations/cyclic";
import { _SERVICE } from "declarations/cyclic/cyclic.did.d.js";
export interface Some<T> {
    __kind__: "Some";
    value: T;
}
export interface None {
    __kind__: "None";
}
export type Option<T> = Some<T> | None;
export type A = Some<B> | None;
export type Z = A;
export type X = Y;
export type C = A;
export type Y = Z;
export type B = Some<C> | None;
export declare const createActor: (canisterId: string | Principal, options?: CreateActorOptions, processError?: (error: unknown) => never) => cyclicInterface;
export declare const canisterId: string;
export interface cyclicInterface {
    f(arg0: A, arg1: B, arg2: C, arg3: X, arg4: Y, arg5: Z): Promise<void>;
}

