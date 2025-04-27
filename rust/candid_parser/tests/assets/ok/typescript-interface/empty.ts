import { empty as _empty, createActor as _createActor, canisterId as _canisterId } from "declarations/empty";
import { type ActorSubclass } from "@dfinity/agent";
import { _SERVICE } from "declarations/empty/empty.did.d.js";
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
export type T = [T];
import { type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export function createActor(canisterId: string | Principal, options?: CreateActorOptions): emptyInterface {
    const actor = _createActor(canisterId, options);
    return new Empty(actor);
}
export const canisterId = _canisterId;
export interface emptyInterface {
    f(arg0: {
    }): Promise<never>;
    g(arg0: T): Promise<{
        a: T;
    }>;
    h(arg0: [T, never]): Promise<{
        a: T;
    } | {
        b: {
        };
    }>;
}
import type { T as _T } from "declarations/empty/empty.did.d.ts";
class Empty implements emptyInterface {
    #actor: ActorSubclass<_SERVICE>;
    constructor(actor?: ActorSubclass<_SERVICE>){
        this.#actor = actor ?? _empty;
    }
    async f(arg0: {
    }): Promise<never> {
        const result = await this.#actor.f(arg0);
        return result;
    }
    async g(arg0: T): Promise<{
        a: T;
    }> {
        const result = await this.#actor.g(to_candid_T_n1(arg0));
        return from_candid_variant_n3(result);
    }
    async h(arg0: [T, never]): Promise<{
        a: T;
    } | {
        b: {
        };
    }> {
        const result = await this.#actor.h(to_candid_tuple_n6(arg0));
        return from_candid_variant_n7(result);
    }
}
export const empty: emptyInterface = new Empty();
function from_candid_variant_n3(value: {
    a: _T;
}): {
    a: T;
} {
    return "a" in value ? {
        a: from_candid_T_n4(value.a)
    } : value;
}
function to_candid_tuple_n6(value: [T, never]): [_T, never] {
    return [
        to_candid_T_n1(value[0]),
        value[1]
    ];
}
function from_candid_variant_n7(value: {
    a: _T;
} | {
    b: [];
}): {
    a: T;
} | {
    b: {
    };
} {
    return "a" in value ? {
        a: from_candid_T_n4(value.a)
    } : "b" in value ? {
        b: value.b
    } : value;
}
function from_candid_tuple_n5(value: [_T]): [T] {
    return [
        from_candid_T_n4(value[0])
    ];
}
function to_candid_tuple_n2(value: [T]): [_T] {
    return [
        to_candid_T_n1(value[0])
    ];
}
function to_candid_T_n1(value: T): _T {
    return to_candid_tuple_n2(value);
}
function from_candid_T_n4(value: _T): T {
    return from_candid_tuple_n5(value);
}

