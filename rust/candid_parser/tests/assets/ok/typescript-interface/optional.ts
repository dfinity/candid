import { type HttpAgentOptions, type ActorConfig, type Agent, type ActorSubclass } from "@dfinity/agent";
import type { Principal } from "@dfinity/principal";
import { optional as _optional, createActor as _createActor, canisterId as _canisterId } from "declarations/optional";
import { _SERVICE } from "declarations/optional/optional.did.d.js";
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
export type option2 = option1 | null;
export type nested = Some<bigint | null> | None;
export type option1 = bigint | null;
export type option3 = option2 | null;
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export function createActor(canisterId: string | Principal, options?: CreateActorOptions, processError?: (error: unknown) => never): optionalInterface {
    const actor = _createActor(canisterId, options);
    return new Optional(actor, processError);
}
export const canisterId = _canisterId;
export interface optionalInterface {
    f(): Promise<[option1, option2]>;
}
import type { option1 as _option1, option2 as _option2 } from "declarations/optional/optional.did.d.ts";
class Optional implements optionalInterface {
    private actor: ActorSubclass<_SERVICE>;
    constructor(actor?: ActorSubclass<_SERVICE>, private processError?: (error: unknown) => never){
        this.actor = actor ?? _optional;
    }
    async f(): Promise<[option1, option2]> {
        if (this.processError) {
            try {
                const result = await this.actor.f();
                return [
                    from_candid_option1_n1(result[0]),
                    from_candid_option2_n3(result[1])
                ];
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.f();
            return [
                from_candid_option1_n1(result[0]),
                from_candid_option2_n3(result[1])
            ];
        }
    }
}
export const optional: optionalInterface = new Optional();
function from_candid_opt_n2(value: [] | [bigint]): bigint | null {
    return value.length === 0 ? null : value[0];
}
function from_candid_opt_n4(value: [] | [_option1]): option1 | null {
    return value.length === 0 ? null : from_candid_option1_n1(value[0]);
}
function from_candid_option1_n1(value: _option1): option1 {
    return from_candid_opt_n2(value);
}
function from_candid_option2_n3(value: _option2): option2 {
    return from_candid_opt_n4(value);
}

