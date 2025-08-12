import { type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
import type { Principal } from "@dfinity/principal";
import { CreateActorOptions } from "declarations/escape";
import { _SERVICE } from "declarations/escape/escape.did.d.js";
export interface Some<T> {
    __kind__: "Some";
    value: T;
}
export interface None {
    __kind__: "None";
}
export type Option<T> = Some<T> | None;
export interface t {
    '\"': bigint;
    '\'': bigint;
    '\"\'': bigint;
    '\\\n\'\"': bigint;
}
export declare const createActor: (canisterId: string | Principal, options?: CreateActorOptions, processError?: (error: unknown) => never) => escapeInterface;
export declare const canisterId: string;
export interface escapeInterface {
    '\n\'\"\'\'\"\"\r\t'(arg0: t): Promise<void>;
}

