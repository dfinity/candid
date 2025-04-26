import { actor as _actor, createActor as _createActor, canisterId as _canisterId } from "declarations/actor";
import { type ActorSubclass } from "@dfinity/agent";
import { _SERVICE } from "declarations/actor/actor.did.d.js";
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
export type f = (arg0: number) => number;
export type g = f;
export type h = (arg0: [Principal, string]) => [Principal, string];
export type o = o | null;
import { type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export function createActor(canisterId: string | Principal, options?: CreateActorOptions): actor {
    const actor = _createActor(canisterId, options);
    return new Actor(actor);
}
export const canisterId = _canisterId;
export interface actor {
    f(arg0: bigint): Promise<[Principal, string]>;
    g: [Principal, string];
    h: [Principal, string];
    o(arg0: o): Promise<o>;
}
import type { o as _o } from "declarations/actor/actor.did.d.ts";
class Actor implements actor {
    #actor: ActorSubclass<_SERVICE>;
    constructor(actor?: ActorSubclass<_SERVICE>){
        this.#actor = actor ?? _actor;
    }
    async f(arg0: bigint): Promise<[Principal, string]> {
        const result = await this.#actor.f(arg0);
        return result;
    }
    async o(arg0: o): Promise<o> {
        const result = await this.#actor.o(to_candid_o_n1(arg0));
        return from_candid_o_n3(result);
    }
}
export const actor: actor = new Actor();
function from_candid_o_n3(value: _o): o {
    return from_candid_opt_n4(value);
}
function to_candid_o_n1(value: o): _o {
    return to_candid_opt_n2(value);
}
function to_candid_opt_n2(value: o | null): [] | [_o] {
    return value === null ? candid_none() : candid_some(to_candid_o_n1(value));
}
function from_candid_opt_n4(value: [] | [_o]): o | null {
    return value.length === 0 ? null : from_candid_o_n3(value[0]);
}

