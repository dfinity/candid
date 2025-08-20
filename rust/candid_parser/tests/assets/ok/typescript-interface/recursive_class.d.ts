import { type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
import type { Principal } from "@dfinity/principal";
import { CreateActorOptions } from "declarations/recursive_class";
import { _SERVICE } from "declarations/recursive_class/recursive_class.did.d.js";
export interface Some<T> {
    __kind__: "Some";
    value: T;
}
export interface None {
    __kind__: "None";
}
export type Option<T> = Some<T> | None;
export interface sInterface {
    next(): Promise<Principal>;
}
export declare const createActor: (canisterId: string | Principal, options?: CreateActorOptions, processError?: (error: unknown) => never) => recursive_classInterface;
export declare const canisterId: string;
export interface recursive_classInterface extends sInterface {
}

