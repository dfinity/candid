import type { Principal } from "@dfinity/principal";
interface Some<T> {
    _tag: "Some";
    value: T;
}
interface None {
    _tag: "None";
}
type Option<T> = Some<T> | None;
export type List = [bigint, List] | null;
export interface Profile {
    age: number;
    name: string;
}
import { type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export declare const createActor: (canisterId: string | Principal, actor?: CreateActorOptions) => class_;
export declare const canisterId: string;
export interface class_ {
    get(): Promise<List>;
    set(arg0: List): Promise<List>;
}

