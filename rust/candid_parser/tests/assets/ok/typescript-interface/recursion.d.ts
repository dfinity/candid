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
export type A = B;
export type B = Some<A> | None;
export type list = node | null;
export interface node {
    head: bigint;
    tail: list;
}
export interface sInterface {
    f: t;
    g(arg0: list): Promise<[B, tree, stream]>;
}
export type stream = {
    head: bigint;
    next: [Principal, string];
} | null;
export type t = (server: Principal) => Promise<void>;
export type tree = {
    __kind__: "branch";
    branch: {
        val: bigint;
        left: tree;
        right: tree;
    };
} | {
    __kind__: "leaf";
    leaf: bigint;
};
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export declare const createActor: (canisterId: string | Principal, options?: CreateActorOptions, processError?: (error: unknown) => never) => recursionInterface;
export declare const canisterId: string;
export interface recursionInterface extends sInterface {
}

