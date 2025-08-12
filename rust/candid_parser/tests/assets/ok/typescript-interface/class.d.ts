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
export type List = [bigint, List] | null;
export interface Profile {
    age: number;
    name: string;
}
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export declare const createActor: (canisterId: string | Principal, options?: CreateActorOptions, processError?: (error: unknown) => never) => classInterface;
export declare const canisterId: string;
/**
 * Doc comment for class service
*/
export interface classInterface {
    /**
     * Doc comment for get method in class service
    */
    get(): Promise<List>;
    set(arg0: List): Promise<List>;
}

