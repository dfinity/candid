import { actor as _actor, createActor as _createActor, canisterId as _canisterId } from "declarations/actor";
import { type ActorSubclass } from "@dfinity/agent";
import { _SERVICE } from "declarations/actor/actor.did.d.js";
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
export type f = (arg0: number) => Promise<number>;
export type g = f;
export type h = (arg0: [Principal, string]) => Promise<[Principal, string]>;
export type o = Some<o> | None;
import { ActorCallError, type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export function createActor(canisterId: string | Principal, options?: CreateActorOptions): actorInterface {
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
    return new Actor(actor);
}
export const canisterId = _canisterId;
export interface actorInterface {
    f(arg0: bigint): Promise<[Principal, string]>;
    g: f;
    h: g;
    h2: h;
    o(arg0: o): Promise<o>;
}
import type { o as _o } from "declarations/actor/actor.did.d.ts";
class Actor implements actorInterface {
    #actor: ActorSubclass<_SERVICE>;
    constructor(actor?: ActorSubclass<_SERVICE>){
        if (actor) {
            this.#actor = actor;
        } else {
            if (process.env.BACKEND_HOST) {
                this.#actor = _createActor(canisterId, {
                    agentOptions: {
                        host: process.env.BACKEND_HOST
                    }
                });
            } else {
                this.#actor = _createActor(canisterId);
            }
        }
    }
    async f(arg0: bigint): Promise<[Principal, string]> {
        try {
            const result = await this.#actor.f(arg0);
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async g(arg0: number): Promise<number> {
        try {
            const result = await this.#actor.g(arg0);
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async h(arg0: number): Promise<number> {
        try {
            const result = await this.#actor.h(arg0);
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async h2(arg0: [Principal, string]): Promise<[Principal, string]> {
        try {
            const result = await this.#actor.h2(arg0);
            return result;
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async o(arg0: o): Promise<o> {
        try {
            const result = await this.#actor.o(to_candid_o_n1(arg0));
            return from_candid_o_n3(result);
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
}
export const actor: actorInterface = new Actor();
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
    return value._tag === "None" ? candid_none() : candid_some(to_candid_o_n1(value.value));
}

