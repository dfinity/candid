import type { Principal } from "@dfinity/principal";
interface Some<T> {
    _tag: "Some";
    value: T;
}
interface None {
    _tag: "None";
}
type Option<T> = Some<T> | None;
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
export declare const createActor: (canisterId: string | Principal, actor?: CreateActorOptions) => escape;
export declare const canisterId: string;
export interface escapeInterface {
    '\n\'\"\'\'\"\"\r\t'(arg0: t): Promise<void>;
}

