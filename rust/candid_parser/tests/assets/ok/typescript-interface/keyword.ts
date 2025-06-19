import { keyword as _keyword, createActor as _createActor, canisterId as _canisterId } from "declarations/keyword";
import { type ActorSubclass } from "@dfinity/agent";
import { _SERVICE } from "declarations/keyword/keyword.did.d.js";
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
export type if_ = {
    branch: {
        val: bigint;
        left: if_;
        right: if_;
    };
} | {
    leaf: bigint;
};
export type list = node | null;
export interface node {
    head: bigint;
    tail: list;
}
export type o = Some<o> | None;
export interface returnInterface {
    f: [Principal, string];
    g(arg0: list): Promise<[if_, stream]>;
}
export type stream = {
    head: bigint;
    next: [Principal, string];
} | null;
export type t = (server: Principal) => void;
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
export async function createActor(options?: CreateActorOptions): Promise<keywordInterface> {
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
    return new Keyword(actor);
}
export const canisterId = _canisterId;
export interface keywordInterface {
    Oneway(): Promise<void>;
    f_(arg0: o): Promise<o>;
    field(arg0: {
        test: number;
        _1291438163_: number;
    }): Promise<{
    }>;
    fieldnat(arg0: {
        _2_: bigint;
        2: bigint;
    }): Promise<[bigint]>;
    oneway(arg0: number): Promise<void>;
    oneway_(arg0: number): Promise<void>;
    query(arg0: Uint8Array | number[]): Promise<Uint8Array | number[]>;
    return_(arg0: o): Promise<o>;
    service: [Principal, string];
    tuple(arg0: [bigint, Uint8Array | number[], string]): Promise<[bigint, number]>;
    variant(arg0: {
        A: null;
    } | {
        B: null;
    } | {
        C: null;
    } | {
        D: number;
    }): Promise<void>;
}
import type { o as _o } from "declarations/keyword/keyword.did.d.ts";
class Keyword implements keywordInterface {
    #actor: ActorSubclass<_SERVICE>;
    constructor(actor: ActorSubclass<_SERVICE>){
        this.#actor = actor;
    }
    async Oneway(): Promise<void> {
        try {
            const result = await this.#actor.Oneway();
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async f_(arg0: o): Promise<o> {
        try {
            const result = await this.#actor.f_(to_candid_o_n1(arg0));
            return from_candid_o_n3(result);
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async field(arg0: {
        test: number;
        _1291438163_: number;
    }): Promise<{
    }> {
        try {
            const result = await this.#actor.field(arg0);
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async fieldnat(arg0: {
        _2_: bigint;
        2: bigint;
    }): Promise<[bigint]> {
        try {
            const result = await this.#actor.fieldnat(arg0);
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async oneway(arg0: number): Promise<void> {
        try {
            const result = await this.#actor.oneway(arg0);
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async oneway_(arg0: number): Promise<void> {
        try {
            const result = await this.#actor.oneway_(arg0);
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async query(arg0: Uint8Array | number[]): Promise<Uint8Array | number[]> {
        try {
            const result = await this.#actor.query(arg0);
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async return_(arg0: o): Promise<o> {
        try {
            const result = await this.#actor.return(to_candid_o_n1(arg0));
            return from_candid_o_n3(result);
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async tuple(arg0: [bigint, Uint8Array | number[], string]): Promise<[bigint, number]> {
        try {
            const result = await this.#actor.tuple(arg0);
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async variant(arg0: {
        A: null;
    } | {
        B: null;
    } | {
        C: null;
    } | {
        D: number;
    }): Promise<void> {
        try {
            const result = await this.#actor.variant(to_candid_variant_n5(arg0));
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
}
function from_candid_o_n3(value: _o): o {
    return from_candid_opt_n4(value);
}
function from_candid_opt_n4(value: [] | [_o]): Some<o> | None {
    return value.length === 0 ? none() : some(from_candid_o_n3(value[0]));
}
function to_candid_o_n1(value: o): _o {
    return to_candid_opt_n2(value);
}
function to_candid_opt_n2(value: Some<o> | None): [] | [_o] {
    return value._tag === "None" ? candid_none() : candid_some(value.value);
}
function to_candid_variant_n5(value: {
    A: null;
} | {
    B: null;
} | {
    C: null;
} | {
    D: number;
}): {
    A: null;
} | {
    B: null;
} | {
    C: null;
} | {
    D: number;
} {
    return "A" in value ? {
        A: value.A
    } : "B" in value ? {
        B: value.B
    } : "C" in value ? {
        C: value.C
    } : "D" in value ? {
        D: value.D
    } : value;
}

