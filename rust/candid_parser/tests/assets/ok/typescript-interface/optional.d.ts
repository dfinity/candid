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
export type option2 = option1 | null;
export type nested = Some<bigint | null> | None;
export type option1 = bigint | null;
export type option3 = option2 | null;
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export declare const createActor: (canisterId: string | Principal, options?: CreateActorOptions, processError?: (error: unknown) => never) => optionalInterface;
export declare const canisterId: string;
export interface optionalInterface {
    f(): Promise<[option1, option2]>;
}

