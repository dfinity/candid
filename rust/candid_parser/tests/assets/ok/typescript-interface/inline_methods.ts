import { inline_methods as _inline_methods, createActor as _createActor, canisterId as _canisterId } from "declarations/inline_methods";
import { type ActorSubclass } from "@dfinity/agent";
import { _SERVICE } from "declarations/inline_methods/inline_methods.did.d.js";
import type { Principal } from "@dfinity/principal";
export interface Some<T> {
    _tag: "Some";
    value: T;
}
export interface None {
    _tag: "None";
}
export type Option<T> = Some<T> | None;
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
function extractAgentErrorMessage(error: string): string {
    const errorString = String(error);
    const match = errorString.match(/with message:\s*'([^']+)'/s);
    return match ? match[1] : errorString;
}
export type Fn = (arg0: bigint) => Promise<bigint>;
export type Gn = Fn;
export interface R {
    x: bigint;
    fn: [Principal, string];
    gn: [Principal, string];
    nested: {
        fn: [Principal, string];
    };
}
export interface RInline {
    x: bigint;
    fn: [Principal, string];
}
import { ActorCallError, type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
async function loadConfig(): Promise<{
    backend_host: string;
    backend_canister_id: string;
}> {
    try {
        const response = await fetch("./env.json");
        const config = await response.json();
        return config;
    } catch  {
        const fallbackConfig = {
            backend_host: "undefined",
            backend_canister_id: "undefined"
        };
        return fallbackConfig;
    }
}
export async function createActor(options?: CreateActorOptions): Promise<inline_methodsInterface> {
    const config = await loadConfig();
    if (!options) {
        options = {};
    }
    if (config.backend_host !== "undefined") {
        options = {
            ...options,
            agentOptions: {
                ...options.agentOptions,
                host: config.backend_host
            }
        };
    }
    let canisterId = _canisterId;
    if (config.backend_canister_id !== "undefined") {
        canisterId = config.backend_canister_id;
    }
    const actor = _createActor(canisterId, options);
    return new Inline_methods(actor);
}
export const canisterId = _canisterId;
export interface inline_methodsInterface {
    add_two(arg0: bigint): Promise<bigint>;
    fn: Fn;
    high_order_fn(arg0: bigint, arg1: [Principal, string]): Promise<bigint>;
    high_order_fn_inline(arg0: bigint, arg1: [Principal, string]): Promise<bigint>;
    high_order_fn_via_id(arg0: bigint, arg1: [Principal, string]): Promise<[Principal, string]>;
    high_order_fn_via_record(arg0: R): Promise<bigint>;
    high_order_fn_via_record_inline(arg0: RInline): Promise<bigint>;
}
class Inline_methods implements inline_methodsInterface {
    #actor: ActorSubclass<_SERVICE>;
    constructor(actor: ActorSubclass<_SERVICE>){
        this.#actor = actor;
    }
    async add_two(arg0: bigint): Promise<bigint> {
        try {
            const result = await this.#actor.add_two(arg0);
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async fn(arg0: bigint): Promise<bigint> {
        try {
            const result = await this.#actor.fn(arg0);
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async high_order_fn(arg0: bigint, arg1: [Principal, string]): Promise<bigint> {
        try {
            const result = await this.#actor.high_order_fn(arg0, arg1);
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async high_order_fn_inline(arg0: bigint, arg1: [Principal, string]): Promise<bigint> {
        try {
            const result = await this.#actor.high_order_fn_inline(arg0, arg1);
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async high_order_fn_via_id(arg0: bigint, arg1: [Principal, string]): Promise<[Principal, string]> {
        try {
            const result = await this.#actor.high_order_fn_via_id(arg0, arg1);
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async high_order_fn_via_record(arg0: R): Promise<bigint> {
        try {
            const result = await this.#actor.high_order_fn_via_record(arg0);
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async high_order_fn_via_record_inline(arg0: RInline): Promise<bigint> {
        try {
            const result = await this.#actor.high_order_fn_via_record_inline(arg0);
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
}

