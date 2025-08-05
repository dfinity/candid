import { type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
import type { Principal } from "@dfinity/principal";
export interface Some<T> {
    _tag: "Some";
    value: T;
}
export interface None {
    _tag: "None";
}
export type Option<T> = Some<T> | None;
export type f = (arg0: number) => Promise<number>;
export type g = f;
export type h = (arg0: [Principal, string]) => Promise<[Principal, string]>;
export type o = Some<o> | None;
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export declare const createActor: (canisterId: string | Principal, actor?: CreateActorOptions) => actorInterface;
export declare const canisterId: string;
export interface actorInterface {
    f(arg0: bigint): Promise<[Principal, string]>;
    g: f;
    h: g;
    h2: h;
    o(arg0: o): Promise<o>;
}

