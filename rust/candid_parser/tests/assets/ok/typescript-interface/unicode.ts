import { type HttpAgentOptions, type ActorConfig, type Agent, type ActorSubclass } from "@dfinity/agent";
import type { Principal } from "@dfinity/principal";
import { unicode as _unicode, createActor as _createActor, canisterId as _canisterId } from "declarations/unicode";
import { _SERVICE } from "declarations/unicode/unicode.did.d.js";
export interface Some<T> {
    __kind__: "Some";
    value: T;
}
export interface None {
    __kind__: "None";
}
export type Option<T> = Some<T> | None;
function some<T>(value: T): Some<T> {
    return {
        __kind__: "Some",
        value: value
    };
}
function none(): None {
    return {
        __kind__: "None"
    };
}
function isNone<T>(option: Option<T>): option is None {
    return option.__kind__ === "None";
}
function isSome<T>(option: Option<T>): option is Some<T> {
    return option.__kind__ === "Some";
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
export function createActor(canisterId: string | Principal, options?: CreateActorOptions, processError?: (error: unknown) => never): unicodeInterface {
    const actor = _createActor(canisterId, options);
    return new Unicode(actor, processError);
}
export const canisterId = _canisterId;
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
import type { B as _B } from "declarations/unicode/unicode.did.d.ts";
class Unicode implements unicodeInterface {
    private actor: ActorSubclass<_SERVICE>;
    constructor(actor?: ActorSubclass<_SERVICE>, private processError?: (error: unknown) => never){
        this.actor = actor ?? _unicode;
    }
    async ""(arg0: bigint): Promise<bigint> {
        if (this.processError) {
            try {
                const result = await this.actor[""](arg0);
                return result;
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor[""](arg0);
            return result;
        }
    }
    async '✈️  🚗 ⛱️ '(): Promise<void> {
        if (this.processError) {
            try {
                const result = await this.actor["✈️  🚗 ⛱️ "]();
                return result;
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor["✈️  🚗 ⛱️ "]();
            return result;
        }
    }
    async '函'(arg0: B): Promise<A> {
        if (this.processError) {
            try {
                const result = await this.actor["函"](to_candid_B_n1(arg0));
                return result;
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor["函"](to_candid_B_n1(arg0));
            return result;
        }
    }
    async '函数名'(arg0: A): Promise<B> {
        if (this.processError) {
            try {
                const result = await this.actor["函数名"](arg0);
                return from_candid_B_n3(result);
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor["函数名"](arg0);
            return from_candid_B_n3(result);
        }
    }
    async '👀'(arg0: bigint): Promise<bigint> {
        if (this.processError) {
            try {
                const result = await this.actor["👀"](arg0);
                return result;
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor["👀"](arg0);
            return result;
        }
    }
}
export const unicode: unicodeInterface = new Unicode();
function from_candid_B_n3(value: _B): B {
    return from_candid_variant_n4(value);
}
function from_candid_variant_n4(value: {
    "": null;
} | {
    '空的': null;
} | {
    '  空的  ': null;
} | {
    '1⃣️2⃣️3⃣️': null;
}): B {
    return "" in value ? B[""] : "空的" in value ? B["空的"] : "  空的  " in value ? B["  空的  "] : "1⃣️2⃣️3⃣️" in value ? B["1⃣️2⃣️3⃣️"] : value;
}
function to_candid_B_n1(value: B): _B {
    return to_candid_variant_n2(value);
}
function to_candid_variant_n2(value: B): {
    "": null;
} | {
    '空的': null;
} | {
    '  空的  ': null;
} | {
    '1⃣️2⃣️3⃣️': null;
} {
    return value == B[""] ? {
        "": null
    } : value == B["空的"] ? {
        '空的': null
    } : value == B["  空的  "] ? {
        '  空的  ': null
    } : value == B["1⃣️2⃣️3⃣️"] ? {
        '1⃣️2⃣️3⃣️': null
    } : value;
}

