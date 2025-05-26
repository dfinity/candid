import type { Principal } from "@dfinity/principal";
export interface Some<T> {
    _tag: "Some";
    value: T;
}
export interface None {
    _tag: "None";
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
    f: [Principal, string];
    g(arg0: list): Promise<[B, tree, stream]>;
}
export type stream = {
    head: bigint;
    next: [Principal, string];
} | null;
export type t = (arg0: Principal) => void;
export type tree = {
    branch: {
        val: bigint;
        left: tree;
        right: tree;
    };
} | {
    leaf: bigint;
};
import { ActorCallError, type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export declare const createActor: (canisterId: string | Principal, actor?: CreateActorOptions) => recursionInterface;
export declare const canisterId: string;
export interface recursionInterface extends sInterface {
}

