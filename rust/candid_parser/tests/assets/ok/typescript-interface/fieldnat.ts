import { type HttpAgentOptions, type ActorConfig, type Agent, type ActorSubclass } from "@dfinity/agent";
import type { Principal } from "@dfinity/principal";
import { fieldnat as _fieldnat, createActor as _createActor, canisterId as _canisterId } from "declarations/fieldnat";
import { _SERVICE } from "declarations/fieldnat/fieldnat.did.d.js";
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
export interface non_tuple {
    _1_: string;
    _2_: string;
}
export type tuple = [string, string];
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export function createActor(canisterId: string | Principal, options?: CreateActorOptions, processError?: (error: unknown) => never): fieldnatInterface {
    const actor = _createActor(canisterId, options);
    return new Fieldnat(actor, processError);
}
export const canisterId = _canisterId;
export enum Variant_e20_e30 {
    e20 = "e20",
    e30 = "e30"
}
export interface fieldnatInterface {
    bab(two: bigint, arg1: bigint): Promise<void>;
    bar(arg0: {
        2: bigint;
    }): Promise<Variant_e20_e30>;
    bas(arg0: [bigint, bigint]): Promise<[string, bigint]>;
    baz(arg0: {
        _2_: bigint;
        2: bigint;
    }): Promise<{
    }>;
    bba(arg0: tuple): Promise<non_tuple>;
    bib(arg0: [bigint]): Promise<{
        _0_: bigint;
    }>;
    foo(arg0: {
        _2_: bigint;
    }): Promise<{
        _2_: bigint;
        _2: bigint;
    }>;
}
class Fieldnat implements fieldnatInterface {
    private actor: ActorSubclass<_SERVICE>;
    constructor(actor?: ActorSubclass<_SERVICE>, private processError?: (error: unknown) => never){
        this.actor = actor ?? _fieldnat;
    }
    async bab(arg0: bigint, arg1: bigint): Promise<void> {
        if (this.processError) {
            try {
                const result = await this.actor.bab(arg0, arg1);
                return result;
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.bab(arg0, arg1);
            return result;
        }
    }
    async bar(arg0: {
        2: bigint;
    }): Promise<Variant_e20_e30> {
        if (this.processError) {
            try {
                const result = await this.actor.bar(arg0);
                return from_candid_variant_n1(result);
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.bar(arg0);
            return from_candid_variant_n1(result);
        }
    }
    async bas(arg0: [bigint, bigint]): Promise<[string, bigint]> {
        if (this.processError) {
            try {
                const result = await this.actor.bas(arg0);
                return result;
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.bas(arg0);
            return result;
        }
    }
    async baz(arg0: {
        _2_: bigint;
        2: bigint;
    }): Promise<{
    }> {
        if (this.processError) {
            try {
                const result = await this.actor.baz(arg0);
                return result;
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.baz(arg0);
            return result;
        }
    }
    async bba(arg0: tuple): Promise<non_tuple> {
        if (this.processError) {
            try {
                const result = await this.actor.bba(arg0);
                return result;
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.bba(arg0);
            return result;
        }
    }
    async bib(arg0: [bigint]): Promise<{
        _0_: bigint;
    }> {
        if (this.processError) {
            try {
                const result = await this.actor.bib(arg0);
                return from_candid_variant_n2(result);
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.bib(arg0);
            return from_candid_variant_n2(result);
        }
    }
    async foo(arg0: {
        _2_: bigint;
    }): Promise<{
        _2_: bigint;
        _2: bigint;
    }> {
        if (this.processError) {
            try {
                const result = await this.actor.foo(arg0);
                return result;
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.foo(arg0);
            return result;
        }
    }
}
export const fieldnat: fieldnatInterface = new Fieldnat();
function from_candid_variant_n1(value: {
    e20: null;
} | {
    e30: null;
}): Variant_e20_e30 {
    return "e20" in value ? Variant_e20_e30.e20 : "e30" in value ? Variant_e20_e30.e30 : value;
}
function from_candid_variant_n2(value: {
    _0_: bigint;
}): {
    _0_: bigint;
} {
    return "_0_" in value ? {
        _0_: value._0_
    } : value;
}

