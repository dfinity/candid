import { service as _service, createActor as _createActor, canisterId as _canisterId } from "declarations/service";
import { type ActorSubclass } from "@dfinity/agent";
import { _SERVICE } from "declarations/service/service.did.d.js";
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
export type Func = () => Promise<Principal>;
export interface ServiceInterface {
    f: Func;
}
export type Service2 = ServiceInterface;
import { ActorCallError, type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
import caffeineEnv from "./env.json" with {
    type: "json"
};
export function createActor(canisterId: string | Principal, options?: CreateActorOptions): serviceInterface {
    if (!options) {
        options = {};
    }
    if (caffeineEnv.backend_host !== "undefined") {
        options = {
            ...options,
            agentOptions: {
                ...options.agentOptions,
                host: caffeineEnv.backend_host
            }
        };
    }
    const actor = _createActor(canisterId, options);
    return new Service(actor);
}
export const canisterId = _canisterId;
export interface serviceInterface {
    asArray(): Promise<[Array<Principal>, Array<[Principal, string]>]>;
    asPrincipal(): Promise<[Principal, [Principal, string]]>;
    asRecord(): Promise<[Principal, Principal | null, [Principal, string]]>;
    asVariant(): Promise<{
        a: Principal;
    } | {
        b: {
            f?: [Principal, string];
        };
    }>;
}
class Service implements serviceInterface {
    #actor: ActorSubclass<_SERVICE>;
    constructor(actor?: ActorSubclass<_SERVICE>){
        if (actor) {
            this.#actor = actor;
        } else {
            if (caffeineEnv.backend_host != "undefined") {
                this.#actor = _createActor(canisterId, {
                    agentOptions: {
                        host: caffeineEnv.backend_host
                    }
                });
            } else {
                this.#actor = _createActor(canisterId);
            }
        }
    }
    async asArray(): Promise<[Array<Principal>, Array<[Principal, string]>]> {
        try {
            const result = await this.#actor.asArray();
            return [
                result[0],
                result[1]
            ];
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async asPrincipal(): Promise<[Principal, [Principal, string]]> {
        try {
            const result = await this.#actor.asPrincipal();
            return [
                result[0],
                result[1]
            ];
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async asRecord(): Promise<[Principal, Principal | null, [Principal, string]]> {
        try {
            const result = await this.#actor.asRecord();
            return from_candid_tuple_n1(result);
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
    async asVariant(): Promise<{
        a: Principal;
    } | {
        b: {
            f?: [Principal, string];
        };
    }> {
        try {
            const result = await this.#actor.asVariant();
            return from_candid_variant_n3(result);
        } catch (e) {
            if (e && typeof e === "object" && "message" in e) {
                throw new Error(extractAgentErrorMessage(e["message"] as string));
            } else throw e;
        }
    }
}
function from_candid_opt_n2(value: [] | [Principal]): Principal | null {
    return value.length === 0 ? null : value[0];
}
function from_candid_opt_n5(value: [] | [[Principal, string]]): [Principal, string] | null {
    return value.length === 0 ? null : value[0];
}
function from_candid_record_n4(value: {
    f: [] | [[Principal, string]];
}): {
    f?: [Principal, string];
} {
    return {
        f: record_opt_to_undefined(from_candid_opt_n5(value.f))
    };
}
function from_candid_tuple_n1(value: [Principal, [] | [Principal], [Principal, string]]): [Principal, Principal | null, [Principal, string]] {
    return [
        value[0],
        from_candid_opt_n2(value[1]),
        value[2]
    ];
}
function from_candid_variant_n3(value: {
    a: Principal;
} | {
    b: {
        f: [] | [[Principal, string]];
    };
}): {
    a: Principal;
} | {
    b: {
        f?: [Principal, string];
    };
} {
    return "a" in value ? {
        a: value.a
    } : "b" in value ? {
        b: from_candid_record_n4(value.b)
    } : value;
}

