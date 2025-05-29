import type { Principal } from "@dfinity/principal";
export interface Some<T> {
    _tag: "Some";
    value: T;
}
export interface None {
    _tag: "None";
}
export type Option<T> = Some<T> | None;
export interface t {
    '\"': bigint;
    '\'': bigint;
    '\"\'': bigint;
    '\\\n\'\"': bigint;
}
import { ActorCallError, type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export declare const createActor: (options?: CreateActorOptions) => Promise<escapeInterface>;
export declare const canisterId: string;
export interface escapeInterface {
    '\n\'\"\'\'\"\"\r\t'(arg0: t): Promise<void>;
}

