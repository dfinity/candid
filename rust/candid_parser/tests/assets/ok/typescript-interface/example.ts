import { example as _example, createActor as _createActor, canisterId as _canisterId } from "declarations/example";
import { type ActorSubclass } from "@dfinity/agent";
import { _SERVICE } from "declarations/example/example.did.d.js";
import type { Principal } from "@dfinity/principal";
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
    find(name: string): Promise<Principal>;
}
export type f = (arg0: List, arg1: [Principal, string]) => Promise<[List | null, res]>;
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
    _41_: Variant__42__A_B_C;
    _42_: bigint;
}
export type nested_res = {
    Ok: Variant_Ok_Err;
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
    f: t;
    g(arg0: list): Promise<[B, tree, stream]>;
}
export type stream = {
    head: bigint;
    next: [Principal, string];
} | null;
export type t = (server: Principal) => Promise<void>;
export type tree = {
    branch: {
        val: bigint;
        left: tree;
        right: tree;
    };
} | {
    leaf: bigint;
};
import { ActorCallError, type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
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
    f: t;
    f1(arg0: list, test: Uint8Array | number[], arg2: boolean | null): Promise<void>;
    g(arg0: list): Promise<[B, tree, stream]>;
    g1(arg0: my_type, arg1: List, arg2: List | null, arg3: nested): Promise<[bigint, Principal, nested_res]>;
    h(arg0: Array<string | null>, arg1: {
        A: bigint;
    } | {
        B: string | null;
    }, arg2: List | null): Promise<{
        _42_: {
        };
        id: bigint;
    }>;
    i: f;
    x(arg0: a, arg1: b): Promise<[a | null, b | null, {
            Ok: {
                result: string;
            };
        } | {
            Err: Variant_a_b;
        }]>;
}
import type { A as _A, B as _B, List as _List, a as _a, b as _b, list as _list, nested as _nested, nested_res as _nested_res, node as _node, res as _res, stream as _stream, tree as _tree } from "declarations/example/example.did.d.ts";
class Example implements exampleInterface {
    private actor: ActorSubclass<_SERVICE>;
    constructor(actor?: ActorSubclass<_SERVICE>, private processError?: (error: unknown) => never){
        this.actor = actor ?? _example;
    }
    async bbbbb(arg0: b): Promise<void> {
        if (this.processError) {
            try {
                const result = await this.actor.bbbbb(arg0);
                return result;
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.bbbbb(arg0);
            return result;
        }
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
    async f1(arg0: list, arg1: Uint8Array | number[], arg2: boolean | null): Promise<void> {
        if (this.processError) {
            try {
                const result = await this.actor.f1(to_candid_list_n1(arg0), arg1, to_candid_opt_n5(arg2));
                return result;
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.f1(to_candid_list_n1(arg0), arg1, to_candid_opt_n5(arg2));
            return result;
        }
    }
    async g(arg0: list): Promise<[B, tree, stream]> {
        if (this.processError) {
            try {
                const result = await this.actor.g(to_candid_list_n1(arg0));
                return [
                    from_candid_B_n6(result[0]),
                    from_candid_tree_n9(result[1]),
                    from_candid_stream_n12(result[2])
                ];
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.g(to_candid_list_n1(arg0));
            return [
                from_candid_B_n6(result[0]),
                from_candid_tree_n9(result[1]),
                from_candid_stream_n12(result[2])
            ];
        }
    }
    async g1(arg0: my_type, arg1: List, arg2: List | null, arg3: nested): Promise<[bigint, Principal, nested_res]> {
        if (this.processError) {
            try {
                const result = await this.actor.g1(arg0, to_candid_List_n14(arg1), to_candid_opt_n17(arg2), to_candid_nested_n18(arg3));
                return [
                    result[0],
                    result[1],
                    from_candid_nested_res_n21(result[2])
                ];
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.g1(arg0, to_candid_List_n14(arg1), to_candid_opt_n17(arg2), to_candid_nested_n18(arg3));
            return [
                result[0],
                result[1],
                from_candid_nested_res_n21(result[2])
            ];
        }
    }
    async h(arg0: Array<string | null>, arg1: {
        A: bigint;
    } | {
        B: string | null;
    }, arg2: List | null): Promise<{
        _42_: {
        };
        id: bigint;
    }> {
        if (this.processError) {
            try {
                const result = await this.actor.h(to_candid_vec_n25(arg0), to_candid_variant_n27(arg1), to_candid_opt_n17(arg2));
                return result;
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.h(to_candid_vec_n25(arg0), to_candid_variant_n27(arg1), to_candid_opt_n17(arg2));
            return result;
        }
    }
    async i(arg0: List, arg1: [Principal, string]): Promise<[List | null, res]> {
        if (this.processError) {
            try {
                const result = await this.actor.i(to_candid_List_n14(arg0), arg1);
                return [
                    from_candid_opt_n28(result[0]),
                    from_candid_res_n32(result[1])
                ];
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.i(to_candid_List_n14(arg0), arg1);
            return [
                from_candid_opt_n28(result[0]),
                from_candid_res_n32(result[1])
            ];
        }
    }
    async x(arg0: a, arg1: b): Promise<[a | null, b | null, {
            Ok: {
                result: string;
            };
        } | {
            Err: Variant_a_b;
        }]> {
        if (this.processError) {
            try {
                const result = await this.actor.x(to_candid_a_n34(arg0), arg1);
                return [
                    from_candid_opt_n36(result[0]),
                    from_candid_opt_n39(result[1]),
                    from_candid_variant_n40(result[2])
                ];
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.x(to_candid_a_n34(arg0), arg1);
            return [
                from_candid_opt_n36(result[0]),
                from_candid_opt_n39(result[1]),
                from_candid_variant_n40(result[2])
            ];
        }
    }
}
export const example: exampleInterface = new Example();
function from_candid_A_n8(value: _A): A {
    return from_candid_opt_n7(value);
}
function from_candid_B_n6(value: _B): B {
    return from_candid_opt_n7(value);
}
function from_candid_List_n29(value: _List): List {
    return from_candid_opt_n30(value);
}
function from_candid_a_n37(value: _a): a {
    return from_candid_variant_n38(value);
}
function from_candid_nested_res_n21(value: _nested_res): nested_res {
    return from_candid_variant_n22(value);
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
function from_candid_opt_n28(value: [] | [_List]): List | null {
    return value.length === 0 ? null : from_candid_List_n29(value[0]);
}
function from_candid_opt_n30(value: [] | [{
        head: bigint;
        tail: _List;
    }]): {
    head: bigint;
    tail: List;
} | null {
    return value.length === 0 ? null : from_candid_record_n31(value[0]);
}
function from_candid_opt_n36(value: [] | [_a]): a | null {
    return value.length === 0 ? null : from_candid_a_n37(value[0]);
}
function from_candid_opt_n39(value: [] | [_b]): b | null {
    return value.length === 0 ? null : value[0];
}
function from_candid_opt_n7(value: [] | [_A]): Some<A> | None {
    return value.length === 0 ? none() : some(from_candid_A_n8(value[0]));
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
function from_candid_record_n31(value: {
    head: bigint;
    tail: _List;
}): {
    head: bigint;
    tail: List;
} {
    return {
        head: value.head,
        tail: from_candid_List_n29(value.tail)
    };
}
function from_candid_res_n32(value: _res): res {
    return from_candid_variant_n33(value);
}
function from_candid_stream_n12(value: _stream): stream {
    return from_candid_opt_n13(value);
}
function from_candid_tree_n9(value: _tree): tree {
    return from_candid_variant_n10(value);
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
function from_candid_variant_n22(value: {
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
}): {
    Ok: Variant_Ok_Err;
} | {
    Err: {
        Ok: {
            content: string;
        };
    } | {
        Err: [bigint];
    };
} {
    return "Ok" in value ? {
        Ok: from_candid_variant_n23(value.Ok)
    } : "Err" in value ? {
        Err: from_candid_variant_n24(value.Err)
    } : value;
}
function from_candid_variant_n23(value: {
    Ok: null;
} | {
    Err: null;
}): Variant_Ok_Err {
    return "Ok" in value ? Variant_Ok_Err.Ok : "Err" in value ? Variant_Ok_Err.Err : value;
}
function from_candid_variant_n24(value: {
    Ok: {
        content: string;
    };
} | {
    Err: [bigint];
}): {
    Ok: {
        content: string;
    };
} | {
    Err: [bigint];
} {
    return "Ok" in value ? {
        Ok: value.Ok
    } : "Err" in value ? {
        Err: value.Err
    } : value;
}
function from_candid_variant_n33(value: {
    Ok: [bigint, bigint];
} | {
    Err: {
        error: string;
    };
}): {
    Ok: [bigint, bigint];
} | {
    Err: {
        error: string;
    };
} {
    return "Ok" in value ? {
        Ok: value.Ok
    } : "Err" in value ? {
        Err: value.Err
    } : value;
}
function from_candid_variant_n38(value: {
    a: null;
} | {
    b: _b;
}): {
    a: null;
} | {
    b: b;
} {
    return "a" in value ? {
        a: value.a
    } : "b" in value ? {
        b: value.b
    } : value;
}
function from_candid_variant_n40(value: {
    Ok: {
        result: string;
    };
} | {
    Err: {
        a: null;
    } | {
        b: null;
    };
}): {
    Ok: {
        result: string;
    };
} | {
    Err: Variant_a_b;
} {
    return "Ok" in value ? {
        Ok: value.Ok
    } : "Err" in value ? {
        Err: from_candid_variant_n41(value.Err)
    } : value;
}
function from_candid_variant_n41(value: {
    a: null;
} | {
    b: null;
}): Variant_a_b {
    return "a" in value ? Variant_a_b.a : "b" in value ? Variant_a_b.b : value;
}
function to_candid_List_n14(value: List): _List {
    return to_candid_opt_n15(value);
}
function to_candid_a_n34(value: a): _a {
    return to_candid_variant_n35(value);
}
function to_candid_list_n1(value: list): _list {
    return to_candid_opt_n2(value);
}
function to_candid_nested_n18(value: nested): _nested {
    return to_candid_record_n19(value);
}
function to_candid_node_n3(value: node): _node {
    return to_candid_record_n4(value);
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
function to_candid_opt_n17(value: List | null): [] | [_List] {
    return value === null ? candid_none() : candid_some(to_candid_List_n14(value));
}
function to_candid_opt_n2(value: node | null): [] | [_node] {
    return value === null ? candid_none() : candid_some(to_candid_node_n3(value));
}
function to_candid_opt_n26(value: string | null): [] | [string] {
    return value === null ? candid_none() : candid_some(value);
}
function to_candid_opt_n5(value: boolean | null): [] | [boolean] {
    return value === null ? candid_none() : candid_some(value);
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
function to_candid_record_n19(value: {
    _0_: bigint;
    _1_: bigint;
    _2_: [bigint, bigint];
    _3_: {
        _0_: bigint;
        _42_: bigint;
        _43_: number;
    };
    _40_: bigint;
    _41_: Variant__42__A_B_C;
    _42_: bigint;
}): {
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
} {
    return {
        _0_: value._0_,
        _1_: value._1_,
        _2_: value._2_,
        _3_: value._3_,
        _40_: value._40_,
        _41_: to_candid_variant_n20(value._41_),
        _42_: value._42_
    };
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
function to_candid_variant_n20(value: Variant__42__A_B_C): {
    _42_: null;
} | {
    A: null;
} | {
    B: null;
} | {
    C: null;
} {
    return value == Variant__42__A_B_C._42_ ? {
        _42_: null
    } : value == Variant__42__A_B_C.A ? {
        A: null
    } : value == Variant__42__A_B_C.B ? {
        B: null
    } : value == Variant__42__A_B_C.C ? {
        C: null
    } : value;
}
function to_candid_variant_n27(value: {
    A: bigint;
} | {
    B: string | null;
}): {
    A: bigint;
} | {
    B: [] | [string];
} {
    return "A" in value ? {
        A: value.A
    } : "B" in value ? {
        B: value.B ? candid_some(value.B) : candid_none()
    } : value;
}
function to_candid_variant_n35(value: {
    a: null;
} | {
    b: b;
}): {
    a: null;
} | {
    b: _b;
} {
    return "a" in value ? {
        a: value.a
    } : "b" in value ? {
        b: value.b
    } : value;
}
function to_candid_vec_n25(value: Array<string | null>): Array<[] | [string]> {
    return value.map((x)=>to_candid_opt_n26(x));
}
export enum Variant_Ok_Err {
    Ok = "Ok",
    Err = "Err"
}
export enum Variant__42__A_B_C {
    _42_ = "_42_",
    A = "A",
    B = "B",
    C = "C"
}
export enum Variant_a_b {
    a = "a",
    b = "b"
}

