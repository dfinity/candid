import { unicode as _unicode, createActor as _createActor, canisterId as _canisterId } from "declarations/unicode";
import { type ActorSubclass } from "@dfinity/agent";
import { _SERVICE } from "declarations/unicode/unicode.did.d.js";
import type { Principal } from "@dfinity/principal";
interface Some<T> {
    _tag: "Some";
    value: T;
}
interface None {
    _tag: "None";
}
type Option<T> = Some<T> | None;
function some<T>(value: T): Some<T> {
    return {
        _tag: "Some",
        value: value
    };
}
function none(): None {
    return {
        _tag: "None"
    };
}
function isNone<T>(option: Option<T>): option is None {
    return option._tag === "None";
}
function isSome<T>(option: Option<T>): option is Some<T> {
    return option._tag === "Some";
}
function unwrap<T>(option: Option<T>): T {
    if (isNone(option)) {
        throw new Error("unwrap: none");
    }
    return option.value;
}
function candid_some<T>(value: T): [T] {
    return [
        value
    ];
}
function candid_none<T>(): [] {
    return [];
}
function record_opt_to_undefined<T>(arg: T | null): T | undefined {
    return arg == null ? undefined : arg;
}
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
export function createActor(canisterId: string | Principal, options?: CreateActorOptions): unicodeInterface {
    const actor = _createActor(canisterId, options);
    return new Unicode(actor);
}
export const canisterId = _canisterId;
export interface unicodeInterface {
    ""(arg0: bigint): Promise<bigint>;
    "✈️  🚗 ⛱️ "(): Promise<void>;
    "函数名"(arg0: A): Promise<B>;
    "👀"(arg0: bigint): Promise<bigint>;
}
class Unicode implements unicodeInterface {
    #actor: ActorSubclass<_SERVICE>;
    constructor(actor?: ActorSubclass<_SERVICE>){
        this.#actor = actor ?? _unicode;
    }
    async ""(arg0: bigint): Promise<bigint> {
        const result = await this.#actor[""](arg0);
        return result;
    }
    async "✈️  🚗 ⛱️ "(): Promise<void> {
        const result = await this.#actor["✈️  🚗 ⛱️ "]();
        return result;
    }
    async "函数名"(arg0: A): Promise<B> {
        const result = await this.#actor["函数名"](arg0);
        return result;
    }
    async "👀"(arg0: bigint): Promise<bigint> {
        const result = await this.#actor["👀"](arg0);
        return result;
    }
}
export const unicode: unicodeInterface = new Unicode();

