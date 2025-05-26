import type { Principal } from "@dfinity/principal";
export interface Some<T> {
    _tag: "Some";
    value: T;
}
export interface None {
    _tag: "None";
}
export type Option<T> = Some<T> | None;
export interface A {
    '\u{e000}': bigint;
    '📦🍦': bigint;
    '字段名': bigint;
    '字 段 名2': bigint;
}
export type B = "" | "空的" | "  空的  " | "1⃣️2⃣️3⃣️";
import { ActorCallError, type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export declare const createActor: (canisterId: string | Principal, actor?: CreateActorOptions) => unicodeInterface;
export declare const canisterId: string;
export interface unicodeInterface {
    ""(arg0: bigint): Promise<bigint>;
    '✈️  🚗 ⛱️ '(): Promise<void>;
    '函数名'(arg0: A): Promise<B>;
    '👀'(arg0: bigint): Promise<bigint>;
}

