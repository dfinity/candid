import type { Principal } from "@dfinity/principal";
interface Some<T> {
    _tag: "Some";
    value: T;
}
interface None {
    _tag: "None";
}
type Option<T> = Some<T> | None;
export type T = [T];
import { type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export declare const createActor: (canisterId: string | Principal, actor?: CreateActorOptions) => empty;
export declare const canisterId: string;
export interface emptyInterface {
    f(arg0: {
    }): Promise<never>;
    g(arg0: T): Promise<"a">;
    h(arg0: [T, never]): Promise<{
        a: T;
    } | {
        b: {
        };
    }>;
}

