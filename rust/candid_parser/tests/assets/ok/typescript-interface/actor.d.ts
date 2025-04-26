import type { Principal } from "@dfinity/principal";
interface Some<T> {
    _tag: "Some";
    value: T;
}
interface None {
    _tag: "None";
}
type Option<T> = Some<T> | None;
export type f = (arg0: number) => number;
export type g = f;
export type h = (arg0: [Principal, string]) => [Principal, string];
export type o = Some<o> | None;
import { type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export declare const createActor: (canisterId: string | Principal, actor?: CreateActorOptions) => actor;
export declare const canisterId: string;
export interface actor {
    f(arg0: bigint): Promise<[Principal, string]>;
    g: [Principal, string];
    h: [Principal, string];
    o(arg0: o): Promise<o>;
}

