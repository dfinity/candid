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
export type T = [T];
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export declare const createActor: (canisterId: string | Principal, options?: CreateActorOptions, processError?: (error: unknown) => never) => emptyInterface;
export declare const canisterId: string;
export interface emptyInterface {
    f(arg0: {
    }): Promise<never>;
    g(arg0: T): Promise<{
        __kind__: "a";
        a: T;
    }>;
    h(arg0: [T, never]): Promise<{
        __kind__: "a";
        a: T;
    } | {
        __kind__: "b";
        b: {
        };
    }>;
}

