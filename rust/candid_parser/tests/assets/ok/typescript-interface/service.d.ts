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
export type Func = () => Promise<Principal>;
export interface ServiceInterface {
    f: Func;
}
export type Service2 = ServiceInterface;
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export declare const createActor: (canisterId: string | Principal, options?: CreateActorOptions, processError?: (error: unknown) => never) => serviceInterface;
export declare const canisterId: string;
export interface serviceInterface {
    asArray(): Promise<[Array<Principal>, Array<[Principal, string]>]>;
    asPrincipal(): Promise<[Principal, [Principal, string]]>;
    asRecord(): Promise<[Principal, Principal | null, [Principal, string]]>;
    asVariant(): Promise<{
        a: Principal;
    } | {
        b: {
            f?: [Principal, string];
        };
    }>;
}

