import { type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
import type { Principal } from "@dfinity/principal";
export interface Some<T> {
    __kind__: "Some";
    value: T;
}
export interface None {
    __kind__: "None";
}
export type Option<T> = Some<T> | None;
export type stream = {
    head: bigint;
    next: [Principal, string];
} | null;
export type if_ = {
    __kind__: "branch";
    branch: {
        val: bigint;
        left: if_;
        right: if_;
    };
} | {
    __kind__: "leaf";
    leaf: bigint;
};
export interface returnInterface {
    f: t;
    g(arg0: list): Promise<[if_, stream]>;
}
export type list = node | null;
export type o = Some<o> | None;
export type t = (server: Principal) => Promise<void>;
export interface node {
    head: bigint;
    tail: list;
}
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export declare const createActor: (canisterId: string | Principal, options?: CreateActorOptions, processError?: (error: unknown) => never) => keywordInterface;
export declare const canisterId: string;
export interface keywordInterface {
    Oneway(): Promise<void>;
    f_(arg0: o): Promise<o>;
    field(arg0: {
        test: number;
        _1291438163_: number;
    }): Promise<{
    }>;
    fieldnat(arg0: {
        _2_: bigint;
        2: bigint;
    }): Promise<[bigint]>;
    oneway(arg0: number): Promise<void>;
    oneway_(arg0: number): Promise<void>;
    query(arg0: Uint8Array | number[]): Promise<Uint8Array | number[]>;
    return_(arg0: o): Promise<o>;
    service: t;
    tuple(arg0: [bigint, Uint8Array | number[], string]): Promise<[bigint, number]>;
    variant(arg0: {
        __kind__: "A";
        A: null;
    } | {
        __kind__: "B";
        B: null;
    } | {
        __kind__: "C";
        C: null;
    } | {
        __kind__: "D";
        D: number;
    }): Promise<void>;
}

