import type { Principal } from "@dfinity/principal";
type Some<T> = {
    _tag: "Some";
    value: T;
};
type None = {
    _tag: "None";
};
type Option<T> = Some<T> | None;
export type Result = {
    ok: bigint;
} | {
    err: string;
};
export interface Tokens {
    e8s: bigint;
}
export interface TransferArgs {
    toPrincipal: Principal;
    amount: Tokens;
    toSubaccount?: Uint8Array | number[];
}
import { type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export declare const createActor: (canisterId: string | Principal, actor?: CreateActorOptions) => backend;
export declare const canisterId: string;
export interface backend {
    transfer(arg0: TransferArgs): Promise<Result>;
}

