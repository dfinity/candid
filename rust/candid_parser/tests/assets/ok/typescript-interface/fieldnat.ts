import { fieldnat as _fieldnat, createActor as _createActor, canisterId as _canisterId } from "declarations/fieldnat";
import { type ActorSubclass } from "@dfinity/agent";
import { _SERVICE } from "declarations/fieldnat/fieldnat.did.d.js";
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
function extractAgentErrorMessage(error: string): string {
    const errorString = String(error);
    const match = errorString.match(/with message: '([^']+)'/);
    return match ? match[1] : errorString;
}
export interface non_tuple {
    _1_: string;
    _2_: string;
}
export type tuple = [string, string];
import { ActorCallError, type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export function createActor(canisterId: string | Principal, options?: CreateActorOptions): fieldnatInterface {
    if (!options) {
        options = {};
    }
    if (process.env.BACKEND_HOST) {
        options = {
            ...options,
            agentOptions: {
                ...options.agentOptions,
                host: process.env.BACKEND_HOST
            }
        };
    }
    const actor = _createActor(canisterId, options);
    return new Fieldnat(actor);
}
export const canisterId = _canisterId;
export interface fieldnatInterface {
    bab(arg0: bigint, arg1: bigint): Promise<void>;
    bar(arg0: {
        2: bigint;
    }): Promise<"e20" | "e30">;
    bas(arg0: [bigint, bigint]): Promise<[string, bigint]>;
    baz(arg0: {
        _2_: bigint;
        2: bigint;
    }): Promise<{
    }>;
    bba(arg0: tuple): Promise<non_tuple>;
    bib(arg0: [bigint]): Promise<"_0">;
    foo(arg0: {
        _2_: bigint;
    }): Promise<{
        _2_: bigint;
        _2: bigint;
    }>;
}
class Fieldnat implements fieldnatInterface {
    #actor: ActorSubclass<_SERVICE>;
    constructor(actor?: ActorSubclass<_SERVICE>){
        if (!actor) {
            this.#actor = _createActor(canisterId, {
                agentOptions: {
                    host: process.env.BACKEND_HOST
                }
            });
        } else {
            this.#actor = actor;
        }
    }
    async bab(arg0: bigint, arg1: bigint): Promise<void> {
        try {
            const result = await this.#actor.bab(arg0, arg1);
            return result;
        } catch (e) {
            if (e instanceof ActorCallError) {
                throw new Error(extractAgentErrorMessage(e.message));
            } else throw e;
        }
    }
    async bar(arg0: {
        2: bigint;
    }): Promise<"e20" | "e30"> {
        try {
            const result = await this.#actor.bar(arg0);
            return from_candid_variant_n1(result);
        } catch (e) {
            if (e instanceof ActorCallError) {
                throw new Error(extractAgentErrorMessage(e.message));
            } else throw e;
        }
    }
    async bas(arg0: [bigint, bigint]): Promise<[string, bigint]> {
        try {
            const result = await this.#actor.bas(arg0);
            return result;
        } catch (e) {
            if (e instanceof ActorCallError) {
                throw new Error(extractAgentErrorMessage(e.message));
            } else throw e;
        }
    }
    async baz(arg0: {
        _2_: bigint;
        2: bigint;
    }): Promise<{
    }> {
        try {
            const result = await this.#actor.baz(arg0);
            return result;
        } catch (e) {
            if (e instanceof ActorCallError) {
                throw new Error(extractAgentErrorMessage(e.message));
            } else throw e;
        }
    }
    async bba(arg0: tuple): Promise<non_tuple> {
        try {
            const result = await this.#actor.bba(arg0);
            return result;
        } catch (e) {
            if (e instanceof ActorCallError) {
                throw new Error(extractAgentErrorMessage(e.message));
            } else throw e;
        }
    }
    async bib(arg0: [bigint]): Promise<"_0"> {
        try {
            const result = await this.#actor.bib(arg0);
            return from_candid_variant_n2(result);
        } catch (e) {
            if (e instanceof ActorCallError) {
                throw new Error(extractAgentErrorMessage(e.message));
            } else throw e;
        }
    }
    async foo(arg0: {
        _2_: bigint;
    }): Promise<{
        _2_: bigint;
        _2: bigint;
    }> {
        try {
            const result = await this.#actor.foo(arg0);
            return result;
        } catch (e) {
            if (e instanceof ActorCallError) {
                throw new Error(extractAgentErrorMessage(e.message));
            } else throw e;
        }
    }
}
export const fieldnat: fieldnatInterface = new Fieldnat();
function from_candid_variant_n1(value: {
    e20: null;
} | {
    e30: null;
}): "e20" | "e30" {
    return "e20" in value ? "e20" : "e30" in value ? "e30" : value;
}
function from_candid_variant_n2(value: {
    _0_: bigint;
}): "_0" {
    return "_0_" in value ? {
        _0_: value._0_
    } : value;
}

