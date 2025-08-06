import { type HttpAgentOptions, type ActorConfig, type Agent, type ActorSubclass } from "@dfinity/agent";
import type { Principal } from "@dfinity/principal";
import { keyword as _keyword, createActor as _createActor, canisterId as _canisterId } from "declarations/keyword";
import { _SERVICE } from "declarations/keyword/keyword.did.d.js";
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
export type stream = {
    head: bigint;
    next: [Principal, string];
} | null;
export type if_ = {
    __kind__: "branch";
    branch: {
        val: bigint;
        left: if_;
        right: if_;
    };
} | {
    __kind__: "leaf";
    leaf: bigint;
};
export interface returnInterface {
    f: t;
    g(arg0: list): Promise<[if_, stream]>;
}
export type list = node | null;
export type o = Some<o> | None;
export type t = (server: Principal) => Promise<void>;
export interface node {
    head: bigint;
    tail: list;
}
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export function createActor(canisterId: string | Principal, options?: CreateActorOptions, processError?: (error: unknown) => never): keywordInterface {
    const actor = _createActor(canisterId, options);
    return new Keyword(actor, processError);
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
    service: t;
    tuple(arg0: [bigint, Uint8Array | number[], string]): Promise<[bigint, number]>;
    variant(arg0: {
        __kind__: "A";
        A: null;
    } | {
        __kind__: "B";
        B: null;
    } | {
        __kind__: "C";
        C: null;
    } | {
        __kind__: "D";
        D: number;
    }): Promise<void>;
}
import type { o as _o } from "declarations/keyword/keyword.did.d.ts";
class Keyword implements keywordInterface {
    private actor: ActorSubclass<_SERVICE>;
    constructor(actor?: ActorSubclass<_SERVICE>, private processError?: (error: unknown) => never){
        this.actor = actor ?? _keyword;
    }
    async Oneway(): Promise<void> {
        if (this.processError) {
            try {
                const result = await this.actor.Oneway();
                return result;
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.Oneway();
            return result;
        }
    }
    async f_(arg0: o): Promise<o> {
        if (this.processError) {
            try {
                const result = await this.actor.f_(to_candid_o_n1(arg0));
                return from_candid_o_n3(result);
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.f_(to_candid_o_n1(arg0));
            return from_candid_o_n3(result);
        }
    }
    async field(arg0: {
        test: number;
        _1291438163_: number;
    }): Promise<{
    }> {
        if (this.processError) {
            try {
                const result = await this.actor.field(arg0);
                return result;
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.field(arg0);
            return result;
        }
    }
    async fieldnat(arg0: {
        _2_: bigint;
        2: bigint;
    }): Promise<[bigint]> {
        if (this.processError) {
            try {
                const result = await this.actor.fieldnat(arg0);
                return result;
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.fieldnat(arg0);
            return result;
        }
    }
    async oneway(arg0: number): Promise<void> {
        if (this.processError) {
            try {
                const result = await this.actor.oneway(arg0);
                return result;
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.oneway(arg0);
            return result;
        }
    }
    async oneway_(arg0: number): Promise<void> {
        if (this.processError) {
            try {
                const result = await this.actor.oneway_(arg0);
                return result;
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.oneway_(arg0);
            return result;
        }
    }
    async query(arg0: Uint8Array | number[]): Promise<Uint8Array | number[]> {
        if (this.processError) {
            try {
                const result = await this.actor.query(arg0);
                return result;
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.query(arg0);
            return result;
        }
    }
    async return_(arg0: o): Promise<o> {
        if (this.processError) {
            try {
                const result = await this.actor.return(to_candid_o_n1(arg0));
                return from_candid_o_n3(result);
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.return(to_candid_o_n1(arg0));
            return from_candid_o_n3(result);
        }
    }
    async service(arg0: Principal): Promise<void> {
        if (this.processError) {
            try {
                const result = await this.actor.service(arg0);
                return result;
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.service(arg0);
            return result;
        }
    }
    async tuple(arg0: [bigint, Uint8Array | number[], string]): Promise<[bigint, number]> {
        if (this.processError) {
            try {
                const result = await this.actor.tuple(arg0);
                return result;
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.tuple(arg0);
            return result;
        }
    }
    async variant(arg0: {
        __kind__: "A";
        A: null;
    } | {
        __kind__: "B";
        B: null;
    } | {
        __kind__: "C";
        C: null;
    } | {
        __kind__: "D";
        D: number;
    }): Promise<void> {
        if (this.processError) {
            try {
                const result = await this.actor.variant(to_candid_variant_n5(arg0));
                return result;
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.variant(to_candid_variant_n5(arg0));
            return result;
        }
    }
}
export const keyword: keywordInterface = new Keyword();
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
    return value.__kind__ === "None" ? candid_none() : candid_some(to_candid_o_n1(value.value));
}
function to_candid_variant_n5(value: {
    __kind__: "A";
    A: null;
} | {
    __kind__: "B";
    B: null;
} | {
    __kind__: "C";
    C: null;
} | {
    __kind__: "D";
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
    return value.__kind__ === "A" ? {
        A: value.A
    } : value.__kind__ === "B" ? {
        B: value.B
    } : value.__kind__ === "C" ? {
        C: value.C
    } : value.__kind__ === "D" ? {
        D: value.D
    } : value;
}

