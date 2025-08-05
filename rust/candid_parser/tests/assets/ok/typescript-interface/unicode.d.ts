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
export interface A {
    '\u{e000}': bigint;
    '📦🍦': bigint;
    '字段名': bigint;
    '字 段 名2': bigint;
}
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export declare const createActor: (canisterId: string | Principal, actor?: CreateActorOptions) => unicodeInterface;
export declare const canisterId: string;
export enum B {
    "" = "",
    '空的' = "空的",
    '  空的  ' = "  空的  ",
    '1⃣️2⃣️3⃣️' = "1⃣️2⃣️3⃣️"
}
export interface unicodeInterface {
    ""(arg0: bigint): Promise<bigint>;
    '✈️  🚗 ⛱️ '(): Promise<void>;
    '函'(arg0: B): Promise<A>;
    '函数名'(arg0: A): Promise<B>;
    '👀'(arg0: bigint): Promise<bigint>;
}

