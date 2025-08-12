import { type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
import type { Principal } from "@dfinity/principal";
import { CreateActorOptions } from "declarations/actor";
import { _SERVICE } from "declarations/actor/actor.did.d.js";
export interface Some<T> {
    __kind__: "Some";
    value: T;
}
export interface None {
    __kind__: "None";
}
export type Option<T> = Some<T> | None;
export type g = f;
export type o = Some<o> | None;
export type f = (arg0: number) => Promise<number>;
export type h = (arg0: [Principal, string]) => Promise<[Principal, string]>;
export declare const createActor: (canisterId: string | Principal, options?: CreateActorOptions, processError?: (error: unknown) => never) => actorInterface;
export declare const canisterId: string;
export interface actorInterface {
    f(arg0: bigint): Promise<[Principal, string]>;
    g: f;
    h: g;
    h2: h;
    o(arg0: o): Promise<o>;
}

