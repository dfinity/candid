import { keyword as _keyword, createActor as _createActor, canisterId as _canisterId } from "declarations/keyword";
import { type ActorSubclass } from "@dfinity/agent";
import { _SERVICE } from "declarations/keyword/keyword.did.d.js";
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
export interface return_ {
    f: [Principal, string];
    g(arg0: list): Promise<[if_, stream]>;
}
export type stream = {
    head: bigint;
    next: [Principal, string];
} | null;
export type t = (arg0: Principal) => void;
import { type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export function createActor(canisterId: string | Principal, options?: CreateActorOptions): keyword {
    const actor = _createActor(canisterId, options);
    return new Keyword(actor);
}
export const canisterId = _canisterId;
export interface keyword {
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
class Keyword implements keyword {
    #actor: ActorSubclass<_SERVICE>;
    constructor(actor?: ActorSubclass<_SERVICE>){
        this.#actor = actor ?? _keyword;
    }
    async Oneway(): Promise<void> {
        const result = await this.#actor.Oneway();
        return result;
    }
    async f_(arg0: o): Promise<o> {
        const result = await this.#actor.f_(to_candid_o_n1(arg0));
        return from_candid_o_n3(result);
    }
    async field(arg0: {
        test: number;
        _1291438163_: number;
    }): Promise<{
    }> {
        const result = await this.#actor.field(arg0);
        return result;
    }
    async fieldnat(arg0: {
        _2_: bigint;
        2: bigint;
    }): Promise<[bigint]> {
        const result = await this.#actor.fieldnat(arg0);
        return result;
    }
    async oneway(arg0: number): Promise<void> {
        const result = await this.#actor.oneway(arg0);
        return result;
    }
    async oneway_(arg0: number): Promise<void> {
        const result = await this.#actor.oneway_(arg0);
        return result;
    }
    async query(arg0: Uint8Array | number[]): Promise<Uint8Array | number[]> {
        const result = await this.#actor.query(arg0);
        return result;
    }
    async return_(arg0: o): Promise<o> {
        const result = await this.#actor.return_(to_candid_o_n1(arg0));
        return from_candid_o_n3(result);
    }
    async tuple(arg0: [bigint, Uint8Array | number[], string]): Promise<[bigint, number]> {
        const result = await this.#actor.tuple(arg0);
        return result;
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
        const result = await this.#actor.variant(arg0);
        return result;
    }
}
export const keyword: keyword = new Keyword();
function from_candid_o_n3(value: _o): o {
    return from_candid_opt_n4(value);
}
function from_candid_opt_n4(value: [] | [_o]): Some<o> | None {
    return value.length === 0 ? none() : some(from_candid_o_n3(value[0]));
}
function to_candid_opt_n2(value: Some<o> | None): [] | [_o] {
    return value._tag === "None" ? candid_none() : candid_some(value.value);
}
function to_candid_o_n1(value: o): _o {
    return to_candid_opt_n2(value);
}

