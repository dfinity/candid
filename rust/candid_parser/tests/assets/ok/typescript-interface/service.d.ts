import type { Principal } from "@dfinity/principal";
interface Some<T> {
    _tag: "Some";
    value: T;
}
interface None {
    _tag: "None";
}
type Option<T> = Some<T> | None;
export type Func = () => Principal;
export interface Service {
    f: [Principal, string];
}
export type Service2 = Service;
import { type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export declare const createActor: (canisterId: string | Principal, actor?: CreateActorOptions) => service;
export declare const canisterId: string;
export interface service {
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

