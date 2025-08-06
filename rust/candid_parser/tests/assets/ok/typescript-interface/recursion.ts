import { type HttpAgentOptions, type ActorConfig, type Agent, type ActorSubclass } from "@dfinity/agent";
import type { Principal } from "@dfinity/principal";
import { recursion as _recursion, createActor as _createActor, canisterId as _canisterId } from "declarations/recursion";
import { _SERVICE } from "declarations/recursion/recursion.did.d.js";
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
export type A = B;
export interface sInterface {
    f: t;
    g(arg0: list): Promise<[B, tree, stream]>;
}
export type B = Some<A> | None;
export type list = node | null;
export type tree = {
    __kind__: "branch";
    branch: {
        val: bigint;
        left: tree;
        right: tree;
    };
} | {
    __kind__: "leaf";
    leaf: bigint;
};
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
export function createActor(canisterId: string | Principal, options?: CreateActorOptions, processError?: (error: unknown) => never): recursionInterface {
    const actor = _createActor(canisterId, options);
    return new Recursion(actor, processError);
}
export const canisterId = _canisterId;
export interface recursionInterface extends sInterface {
}
import type { A as _A, B as _B, list as _list, node as _node, stream as _stream, tree as _tree } from "declarations/recursion/recursion.did.d.ts";
class Recursion implements recursionInterface {
    private actor: ActorSubclass<_SERVICE>;
    constructor(actor?: ActorSubclass<_SERVICE>, private processError?: (error: unknown) => never){
        this.actor = actor ?? _recursion;
    }
    async f(arg0: Principal): Promise<void> {
        if (this.processError) {
            try {
                const result = await this.actor.f(arg0);
                return result;
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.f(arg0);
            return result;
        }
    }
    async g(arg0: list): Promise<[B, tree, stream]> {
        if (this.processError) {
            try {
                const result = await this.actor.g(to_candid_list_n1(arg0));
                return [
                    from_candid_B_n5(result[0]),
                    from_candid_tree_n8(result[1]),
                    from_candid_stream_n11(result[2])
                ];
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.g(to_candid_list_n1(arg0));
            return [
                from_candid_B_n5(result[0]),
                from_candid_tree_n8(result[1]),
                from_candid_stream_n11(result[2])
            ];
        }
    }
}
export const recursion: recursionInterface = new Recursion();
function from_candid_A_n7(value: _A): A {
    return from_candid_opt_n6(value);
}
function from_candid_B_n5(value: _B): B {
    return from_candid_opt_n6(value);
}
function from_candid_opt_n12(value: [] | [{
        head: bigint;
        next: [Principal, string];
    }]): {
    head: bigint;
    next: [Principal, string];
} | null {
    return value.length === 0 ? null : value[0];
}
function from_candid_opt_n6(value: [] | [_A]): Some<A> | None {
    return value.length === 0 ? none() : some(from_candid_A_n7(value[0]));
}
function from_candid_record_n10(value: {
    val: bigint;
    left: _tree;
    right: _tree;
}): {
    val: bigint;
    left: tree;
    right: tree;
} {
    return {
        val: value.val,
        left: from_candid_tree_n8(value.left),
        right: from_candid_tree_n8(value.right)
    };
}
function from_candid_stream_n11(value: _stream): stream {
    return from_candid_opt_n12(value);
}
function from_candid_tree_n8(value: _tree): tree {
    return from_candid_variant_n9(value);
}
function from_candid_variant_n9(value: {
    branch: {
        val: bigint;
        left: _tree;
        right: _tree;
    };
} | {
    leaf: bigint;
}): {
    __kind__: "branch";
    branch: {
        val: bigint;
        left: tree;
        right: tree;
    };
} | {
    __kind__: "leaf";
    leaf: bigint;
} {
    return "branch" in value ? {
        __kind__: "branch",
        branch: from_candid_record_n10(value.branch)
    } : "leaf" in value ? {
        __kind__: "leaf",
        leaf: value.leaf
    } : value;
}
function to_candid_list_n1(value: list): _list {
    return to_candid_opt_n2(value);
}
function to_candid_node_n3(value: node): _node {
    return to_candid_record_n4(value);
}
function to_candid_opt_n2(value: node | null): [] | [_node] {
    return value === null ? candid_none() : candid_some(to_candid_node_n3(value));
}
function to_candid_record_n4(value: {
    head: bigint;
    tail: list;
}): {
    head: bigint;
    tail: _list;
} {
    return {
        head: value.head,
        tail: to_candid_list_n1(value.tail)
    };
}

