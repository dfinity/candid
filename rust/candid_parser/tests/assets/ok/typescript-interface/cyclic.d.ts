import type { Principal } from "@dfinity/principal";
interface Some<T> {
    _tag: "Some";
    value: T;
}
interface None {
    _tag: "None";
}
type Option<T> = Some<T> | None;
export type A = B | null;
export type B = C | null;
export type C = A;
export type X = Y;
export type Y = Z;
export type Z = A;
import { type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export declare const createActor: (canisterId: string | Principal, actor?: CreateActorOptions) => cyclic;
export declare const canisterId: string;
export interface cyclic {
    f(arg0: A, arg1: B, arg2: C, arg3: X, arg4: Y, arg5: Z): Promise<void>;
}

