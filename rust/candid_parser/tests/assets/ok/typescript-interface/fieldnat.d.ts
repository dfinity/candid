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
import { ActorCallError, type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export declare const createActor: (options?: CreateActorOptions) => Promise<fieldnatInterface>;
export declare const canisterId: string;
export interface fieldnatInterface {
    bab(two: bigint, arg1: bigint): Promise<void>;
    bar(arg0: {
        2: bigint;
    }): Promise<"e20" | "e30">;
    bas(arg0: [bigint, bigint]): Promise<[string, bigint]>;
    baz(arg0: {
        _2_: bigint;
        2: bigint;
    }): Promise<{
    }>;
    bba(arg0: tuple): Promise<non_tuple>;
    bib(arg0: [bigint]): Promise<"_0">;
    foo(arg0: {
        _2_: bigint;
    }): Promise<{
        _2_: bigint;
        _2: bigint;
    }>;
}

