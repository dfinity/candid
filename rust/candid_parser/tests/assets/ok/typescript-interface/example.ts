import { example as _example, createActor as _createActor, canisterId as _canisterId } from "declarations/example";
import { type ActorSubclass } from "@dfinity/agent";
import { _SERVICE } from "declarations/example/example.did.d.js";
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
export type A = B;
export type B = Some<A> | None;
export type List = {
    head: bigint;
    tail: List;
} | null;
export type a = {
    a: null;
} | {
    b: b;
};
export type b = [bigint, bigint];
export interface brokerInterface {
    find(arg0: string): Promise<Principal>;
}
export type f = (arg0: List, arg1: [Principal, string]) => [List | null, res];
export type list = node | null;
export type my_type = Principal;
export interface nested {
    _0_: bigint;
    _1_: bigint;
    _2_: [bigint, bigint];
    _3_: {
        _0_: bigint;
        _42_: bigint;
        _43_: number;
    };
    _40_: bigint;
    _41_: {
        _42_: null;
    } | {
        A: null;
    } | {
        B: null;
    } | {
        C: null;
    };
    _42_: bigint;
}
export type nested_res = {
    Ok: {
        Ok: null;
    } | {
        Err: null;
    };
} | {
    Err: {
        Ok: {
            content: string;
        };
    } | {
        Err: [bigint];
    };
};
export interface node {
    head: bigint;
    tail: list;
}
export type res = {
    Ok: [bigint, bigint];
} | {
    Err: {
        error: string;
    };
};
export interface sInterface {
    f: [Principal, string];
    g(arg0: list): Promise<[B, tree, stream]>;
}
export type stream = {
    head: bigint;
    next: [Principal, string];
} | null;
export type t = (arg0: Principal) => void;
export type tree = {
    branch: {
        val: bigint;
        left: tree;
        right: tree;
    };
} | {
    leaf: bigint;
};
import { type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export function createActor(canisterId: string | Principal, options?: CreateActorOptions): exampleInterface {
    const actor = _createActor(canisterId, options);
    return new Example(actor);
}
export const canisterId = _canisterId;
export interface exampleInterface {
    bbbbb(arg0: b): Promise<void>;
    f: [Principal, string];
    f1(arg0: list, arg1: Uint8Array | number[], arg2: boolean | null): Promise<void>;
    g(arg0: list): Promise<[B, tree, stream]>;
    g1(arg0: my_type, arg1: List, arg2: List | null, arg3: nested): Promise<[bigint, Principal, nested_res]>;
    h(arg0: Array<string | null>, arg1: {
        A: bigint;
    } | {
        B?: string;
    }, arg2: List | null): Promise<{
        _42_: {
        };
        id: bigint;
    }>;
    i: [Principal, string];
    x(arg0: a, arg1: b): Promise<[a | null, b | null, {
            Ok: {
                result: string;
            };
        } | {
            Err: {
                a: null;
            } | {
                b: null;
            };
        }]>;
}
import type { stream as _stream, B as _B, b as _b, list as _list, tree as _tree, a as _a, node as _node, List as _List, A as _A } from "declarations/example/example.did.d.ts";
class Example implements exampleInterface {
    #actor: ActorSubclass<_SERVICE>;
    constructor(actor?: ActorSubclass<_SERVICE>){
        this.#actor = actor ?? _example;
    }
    async bbbbb(arg0: b): Promise<void> {
        const result = await this.#actor.bbbbb(arg0);
        return result;
    }
    async f1(arg0: list, arg1: Uint8Array | number[], arg2: boolean | null): Promise<void> {
        const result = await this.#actor.f1(to_candid_list_n1(arg0), arg1, to_candid_opt_n5(arg2));
        return result;
    }
    async g(arg0: list): Promise<[B, tree, stream]> {
        const result = await this.#actor.g(to_candid_list_n1(arg0));
        return [
            from_candid_B_n6(result[0]),
            from_candid_tree_n9(result[1]),
            from_candid_stream_n12(result[2])
        ];
    }
    async g1(arg0: my_type, arg1: List, arg2: List | null, arg3: nested): Promise<[bigint, Principal, nested_res]> {
        const result = await this.#actor.g1(arg0, to_candid_List_n14(arg1), to_candid_opt_n17(arg2), arg3);
        return [
            result[0],
            result[1],
            result[2]
        ];
    }
    async h(arg0: Array<string | null>, arg1: {
        A: bigint;
    } | {
        B?: string;
    }, arg2: List | null): Promise<{
        _42_: {
        };
        id: bigint;
    }> {
        const result = await this.#actor.h(to_candid_vec_n18(arg0), to_candid_variant_n20(arg1), to_candid_opt_n17(arg2));
        return result;
    }
    async x(arg0: a, arg1: b): Promise<[a | null, b | null, {
            Ok: {
                result: string;
            };
        } | {
            Err: {
                a: null;
            } | {
                b: null;
            };
        }]> {
        const result = await this.#actor.x(arg0, arg1);
        return [
            from_candid_opt_n21(result[0]),
            from_candid_opt_n22(result[1]),
            result[2]
        ];
    }
}
export const example: exampleInterface = new Example();
function from_candid_A_n8(value: _A): A {
    return from_candid_opt_n7(value);
}
function from_candid_opt_n22(value: [] | [_b]): b | null {
    return value.length === 0 ? null : value[0];
}
function to_candid_opt_n2(value: node | null): [] | [_node] {
    return value === null ? candid_none() : candid_some(to_candid_node_n3(value));
}
function to_candid_list_n1(value: list): _list {
    return to_candid_opt_n2(value);
}
function from_candid_record_n11(value: {
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
        left: from_candid_tree_n9(value.left),
        right: from_candid_tree_n9(value.right)
    };
}
function from_candid_variant_n10(value: {
    branch: {
        val: bigint;
        left: _tree;
        right: _tree;
    };
} | {
    leaf: bigint;
}): {
    branch: {
        val: bigint;
        left: tree;
        right: tree;
    };
} | {
    leaf: bigint;
} {
    return "branch" in value ? {
        branch: from_candid_record_n11(value.branch)
    } : "leaf" in value ? {
        leaf: value.leaf
    } : value;
}
function to_candid_opt_n17(value: List | null): [] | [_List] {
    return value === null ? candid_none() : candid_some(to_candid_List_n14(value));
}
function to_candid_opt_n19(value: string | null): [] | [string] {
    return value === null ? candid_none() : candid_some(value);
}
function from_candid_tree_n9(value: _tree): tree {
    return from_candid_variant_n10(value);
}
function to_candid_variant_n20(value: {
    A: bigint;
} | {
    B?: string;
}): {
    A: bigint;
} | {
    B: [] | [string];
} {
    return "A" in value ? {
        A: value.A
    } : "B" in value ? {
        B: to_candid_opt_n19(value.B)
    } : value;
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
function from_candid_stream_n12(value: _stream): stream {
    return from_candid_opt_n13(value);
}
function to_candid_record_n16(value: {
    head: bigint;
    tail: List;
}): {
    head: bigint;
    tail: _List;
} {
    return {
        head: value.head,
        tail: to_candid_List_n14(value.tail)
    };
}
function to_candid_vec_n18(value: Array<string | null>): Array<[] | [string]> {
    return value.map((x)=>to_candid_opt_n19(x));
}
function to_candid_opt_n5(value: boolean | null): [] | [boolean] {
    return value === null ? candid_none() : candid_some(value);
}
function to_candid_opt_n15(value: {
    head: bigint;
    tail: List;
} | null): [] | [{
        head: bigint;
        tail: _List;
    }] {
    return value === null ? candid_none() : candid_some(to_candid_record_n16(value));
}
function to_candid_node_n3(value: node): _node {
    return to_candid_record_n4(value);
}
function from_candid_opt_n13(value: [] | [{
        head: bigint;
        next: [Principal, string];
    }]): {
    head: bigint;
    next: [Principal, string];
} | null {
    return value.length === 0 ? null : value[0];
}
function from_candid_B_n6(value: _B): B {
    return from_candid_opt_n7(value);
}
function to_candid_List_n14(value: List): _List {
    return to_candid_opt_n15(value);
}
function from_candid_opt_n21(value: [] | [_a]): a | null {
    return value.length === 0 ? null : value[0];
}
function from_candid_opt_n7(value: [] | [_A]): Some<A> | None {
    return value.length === 0 ? none() : some(from_candid_A_n8(value[0]));
}

