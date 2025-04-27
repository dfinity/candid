import type { Principal } from "@dfinity/principal";
interface Some<T> {
    _tag: "Some";
    value: T;
}
interface None {
    _tag: "None";
}
type Option<T> = Some<T> | None;
export interface A {
    "": bigint;
    "📦🍦": bigint;
    "字段名": bigint;
    "字 段 名2": bigint;
}
export type B = {
    "": null;
} | {
    "空的": null;
} | {
    "  空的  ": null;
} | {
    "1⃣️2⃣️3⃣️": null;
};
import { type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export declare const createActor: (canisterId: string | Principal, actor?: CreateActorOptions) => unicode;
export declare const canisterId: string;
export interface unicodeInterface {
    ""(arg0: bigint): Promise<bigint>;
    "✈️  🚗 ⛱️ "(): Promise<void>;
    "函数名"(arg0: A): Promise<B>;
    "👀"(arg0: bigint): Promise<bigint>;
}

