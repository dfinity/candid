import type { Principal } from "@dfinity/principal";
export interface Some<T> {
    _tag: "Some";
    value: T;
}
export interface None {
    _tag: "None";
}
export type Option<T> = Some<T> | None;
export type List = [bigint, List] | null;
export interface Profile {
    age: number;
    name: string;
}
import { ActorCallError, type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export declare const createActor: (options?: CreateActorOptions) => Promise<classInterface>;
export declare const canisterId: string;
export interface classInterface {
    get(): Promise<List>;
    set(arg0: List): Promise<List>;
}

