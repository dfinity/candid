import { service as _service, createActor as _createActor, canisterId as _canisterId } from "declarations/service";
import { type ActorSubclass } from "@dfinity/agent";
import { _SERVICE } from "declarations/service/service.did.d.js";
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
export type Func = () => Principal;
export interface ServiceInterface {
    f: [Principal, string];
}
export type Service2 = Service;
import { type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export function createActor(canisterId: string | Principal, options?: CreateActorOptions): serviceInterface {
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
import type { Func as _Func, Service as _Service, Service2 as _Service2 } from "declarations/service/service.did.d.ts";
class Service implements serviceInterface {
    #actor: ActorSubclass<_SERVICE>;
    constructor(actor?: ActorSubclass<_SERVICE>){
        this.#actor = actor ?? _service;
    }
    async asArray(): Promise<[Array<Principal>, Array<[Principal, string]>]> {
        const result = await this.#actor.asArray();
        return [
            result[0],
            result[1]
        ];
    }
    async asPrincipal(): Promise<[Principal, [Principal, string]]> {
        const result = await this.#actor.asPrincipal();
        return [
            result[0],
            result[1]
        ];
    }
    async asRecord(): Promise<[Principal, Principal | null, [Principal, string]]> {
        const result = await this.#actor.asRecord();
        return from_candid_tuple_n1(result);
    }
    async asVariant(): Promise<{
        a: Principal;
    } | {
        b: {
            f?: [Principal, string];
        };
    }> {
        const result = await this.#actor.asVariant();
        return from_candid_variant_n3(result);
    }
}
export const service: serviceInterface = new Service();
function from_candid_opt_n2(value: [] | [_Service]): Principal | null {
    return value.length === 0 ? null : value[0];
}
function from_candid_opt_n5(value: [] | [_Func]): [Principal, string] | null {
    return value.length === 0 ? null : value[0];
}
function from_candid_record_n4(value: {
    f: [] | [_Func];
}): {
    f?: [Principal, string];
} {
    return {
        f: record_opt_to_undefined(from_candid_opt_n5(value.f))
    };
}
function from_candid_tuple_n1(value: [_Service2, [] | [_Service], _Func]): [Principal, Principal | null, [Principal, string]] {
    return [
        value[0],
        from_candid_opt_n2(value[1]),
        value[2]
    ];
}
function from_candid_variant_n3(value: {
    a: _Service2;
} | {
    b: {
        f: [] | [_Func];
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

