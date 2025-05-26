import type { Principal } from "@dfinity/principal";
export interface Some<T> {
    _tag: "Some";
    value: T;
}
export interface None {
    _tag: "None";
}
export type Option<T> = Some<T> | None;
export type f = (arg0: number) => number;
export type g = f;
export type h = (arg0: [Principal, string]) => [Principal, string];
export type o = Some<o> | None;
import { ActorCallError, type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export declare const createActor: (canisterId: string | Principal, actor?: CreateActorOptions) => actorInterface;
export declare const canisterId: string;
export interface actorInterface {
    f(arg0: bigint): Promise<[Principal, string]>;
    g: [Principal, string];
    h: [Principal, string];
    o(arg0: o): Promise<o>;
}

