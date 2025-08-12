import { type HttpAgentOptions, type ActorConfig, type Agent, type ActorSubclass } from "@dfinity/agent";
import type { Principal } from "@dfinity/principal";
import { inline_methods as _inline_methods, createActor as _createActor, canisterId as _canisterId, CreateActorOptions } from "declarations/inline_methods";
import { _SERVICE } from "declarations/inline_methods/inline_methods.did.d.js";
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
export type Fn = (arg0: bigint) => Promise<bigint>;
export interface R {
    x: bigint;
    fn: [Principal, string];
    gn: [Principal, string];
    nested: {
        fn: [Principal, string];
    };
}
export interface RInline {
    x: bigint;
    fn: [Principal, string];
}
export type Gn = Fn;
export function createActor(canisterId: string | Principal, options?: CreateActorOptions, processError?: (error: unknown) => never): inline_methodsInterface {
    const actor = _createActor(canisterId, options);
    return new Inline_methods(actor, processError);
}
export const canisterId = _canisterId;
export interface inline_methodsInterface {
    add_two(arg0: bigint): Promise<bigint>;
    fn: Fn;
    high_order_fn(arg0: bigint, arg1: [Principal, string]): Promise<bigint>;
    high_order_fn_inline(arg0: bigint, arg1: [Principal, string]): Promise<bigint>;
    high_order_fn_via_id(arg0: bigint, arg1: [Principal, string]): Promise<[Principal, string]>;
    high_order_fn_via_record(arg0: R): Promise<bigint>;
    high_order_fn_via_record_inline(arg0: RInline): Promise<bigint>;
}
class Inline_methods implements inline_methodsInterface {
    private actor: ActorSubclass<_SERVICE>;
    constructor(actor?: ActorSubclass<_SERVICE>, private processError?: (error: unknown) => never){
        this.actor = actor ?? _inline_methods;
    }
    async add_two(arg0: bigint): Promise<bigint> {
        if (this.processError) {
            try {
                const result = await this.actor.add_two(arg0);
                return result;
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.add_two(arg0);
            return result;
        }
    }
    async fn(arg0: bigint): Promise<bigint> {
        if (this.processError) {
            try {
                const result = await this.actor.fn(arg0);
                return result;
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.fn(arg0);
            return result;
        }
    }
    async high_order_fn(arg0: bigint, arg1: [Principal, string]): Promise<bigint> {
        if (this.processError) {
            try {
                const result = await this.actor.high_order_fn(arg0, arg1);
                return result;
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.high_order_fn(arg0, arg1);
            return result;
        }
    }
    async high_order_fn_inline(arg0: bigint, arg1: [Principal, string]): Promise<bigint> {
        if (this.processError) {
            try {
                const result = await this.actor.high_order_fn_inline(arg0, arg1);
                return result;
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.high_order_fn_inline(arg0, arg1);
            return result;
        }
    }
    async high_order_fn_via_id(arg0: bigint, arg1: [Principal, string]): Promise<[Principal, string]> {
        if (this.processError) {
            try {
                const result = await this.actor.high_order_fn_via_id(arg0, arg1);
                return result;
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.high_order_fn_via_id(arg0, arg1);
            return result;
        }
    }
    async high_order_fn_via_record(arg0: R): Promise<bigint> {
        if (this.processError) {
            try {
                const result = await this.actor.high_order_fn_via_record(arg0);
                return result;
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.high_order_fn_via_record(arg0);
            return result;
        }
    }
    async high_order_fn_via_record_inline(arg0: RInline): Promise<bigint> {
        if (this.processError) {
            try {
                const result = await this.actor.high_order_fn_via_record_inline(arg0);
                return result;
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.high_order_fn_via_record_inline(arg0);
            return result;
        }
    }
}
export const inline_methods: inline_methodsInterface = new Inline_methods();

