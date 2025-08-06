import { type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
import type { Principal } from "@dfinity/principal";
export interface Some<T> {
    _tag: "Some";
    value: T;
}
export interface None {
    _tag: "None";
}
export type Option<T> = Some<T> | None;
export interface non_tuple {
    _1_: string;
    _2_: string;
}
export type tuple = [string, string];
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export declare const createActor: (canisterId: string | Principal, options?: CreateActorOptions, processError?: (error: unknown) => never) => fieldnatInterface;
export declare const canisterId: string;
export enum Variant_e20_e30 {
    e20 = "e20",
    e30 = "e30"
}
export interface fieldnatInterface {
    bab(two: bigint, arg1: bigint): Promise<void>;
    bar(arg0: {
        2: bigint;
    }): Promise<Variant_e20_e30>;
    bas(arg0: [bigint, bigint]): Promise<[string, bigint]>;
    baz(arg0: {
        _2_: bigint;
        2: bigint;
    }): Promise<{
    }>;
    bba(arg0: tuple): Promise<non_tuple>;
    bib(arg0: [bigint]): Promise<{
        __kind__: "_0_";
        _0_: bigint;
    }>;
    foo(arg0: {
        _2_: bigint;
    }): Promise<{
        _2_: bigint;
        _2: bigint;
    }>;
}

