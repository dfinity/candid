import { type HttpAgentOptions, type ActorConfig, type Agent, type ActorSubclass } from "@dfinity/agent";
import type { Principal } from "@dfinity/principal";
import { example as _example, createActor as _createActor, canisterId as _canisterId } from "declarations/example";
import { _SERVICE } from "declarations/example/example.did.d.js";
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
export type my_variant = {
    /**
     * Doc comment for my_variant field a
    */
    __kind__: "a";
    a: {
        /**
         * Doc comment for my_variant field a field b
        */
        b: string;
    };
} | {
    /**
     * Doc comment for my_variant field c
    */
    __kind__: "c";
    c: {
        d: string;
        e: Array<{
            f: bigint;
        }>;
    } | null;
};
export interface sInterface {
    f: t;
    g(arg0: list): Promise<[B, tree, stream]>;
}
/**
 * Doc comment for List
*/
export type List = {
    head: bigint;
    tail: List;
} | null;
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
export type a = {
    __kind__: "a";
    a: null;
} | {
    __kind__: "b";
    b: b;
};
export interface brokerInterface {
    find(name: string): Promise<Principal>;
}
export type t = (server: Principal) => Promise<void>;
/**
 * Doc comment for prim type
*/
export type my_type = Principal;
export type f = (arg0: List, arg1: [Principal, string]) => Promise<[List | null, res]>;
export type b = [bigint, bigint];
export type stream = {
    head: bigint;
    next: [Principal, string];
} | null;
export type A = B;
export interface nested {
    _0_: bigint;
    _1_: bigint;
    /**
     * Doc comment for nested record
    */
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
    __kind__: "Ok";
    Ok: Variant_Ok_Err;
} | {
    __kind__: "Err";
    Err: {
        /**
         * Doc comment for Ok in nested variant
        */
        __kind__: "Ok";
        Ok: {
            content: string;
        };
    } | {
        /**
         * Doc comment for Err in nested variant
        */
        __kind__: "Err";
        Err: [bigint];
    };
};
export interface nested_records {
    /**
     * Doc comment for nested_records field nested
    */
    nested?: {
        nested_field: string;
    };
}
export type B = Some<A> | None;
export type res = {
    /**
     * Doc comment for Ok variant
    */
    __kind__: "Ok";
    Ok: [bigint, bigint];
} | {
    /**
     * Doc comment for Err variant
    */
    __kind__: "Err";
    Err: {
        /**
         * Doc comment for error field in Err variant,
         * on multiple lines
        */
        error: string;
    };
};
export interface node {
    head: bigint;
    tail: list;
}
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export function createActor(canisterId: string | Principal, options?: CreateActorOptions, processError?: (error: unknown) => never): exampleInterface {
    const actor = _createActor(canisterId, options);
    return new Example(actor, processError);
}
export const canisterId = _canisterId;
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
/**
 * Doc comment for service
*/
export interface exampleInterface {
    /**
     * Doc comment for f1 method of service
    */
    f1(arg0: list, test: Uint8Array | number[], arg2: boolean | null): Promise<void>;
    g1(arg0: my_type, arg1: List, arg2: List | null, arg3: nested): Promise<[bigint, Principal, nested_res]>;
    h(arg0: Array<string | null>, arg1: {
        __kind__: "A";
        A: bigint;
    } | {
        __kind__: "B";
        B: string | null;
    }, arg2: List | null): Promise<{
        _42_: {
        };
        id: bigint;
    }>;
    /**
     * Doc comment for i method of service
    */
    i: f;
    x(arg0: a, arg1: b): Promise<[a | null, b | null, {
            __kind__: "Ok";
            Ok: {
                result: string;
            };
        } | {
            __kind__: "Err";
            Err: Variant_a_b;
        }]>;
    y(arg0: nested_records): Promise<[nested_records, my_variant]>;
    f: t;
    g(arg0: list): Promise<[B, tree, stream]>;
    /**
     * Doc comment for imported bbbbb service method
    */
    bbbbb(arg0: b): Promise<void>;
}
import type { A as _A, B as _B, List as _List, a as _a, b as _b, list as _list, my_variant as _my_variant, nested as _nested, nested_records as _nested_records, nested_res as _nested_res, node as _node, res as _res, stream as _stream, tree as _tree } from "declarations/example/example.did.d.ts";
class Example implements exampleInterface {
    private actor: ActorSubclass<_SERVICE>;
    constructor(actor?: ActorSubclass<_SERVICE>, private processError?: (error: unknown) => never){
        this.actor = actor ?? _example;
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
    async g1(arg0: my_type, arg1: List, arg2: List | null, arg3: nested): Promise<[bigint, Principal, nested_res]> {
        if (this.processError) {
            try {
                const result = await this.actor.g1(arg0, to_candid_List_n6(arg1), to_candid_opt_n9(arg2), to_candid_nested_n10(arg3));
                return [
                    result[0],
                    result[1],
                    from_candid_nested_res_n13(result[2])
                ];
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.g1(arg0, to_candid_List_n6(arg1), to_candid_opt_n9(arg2), to_candid_nested_n10(arg3));
            return [
                result[0],
                result[1],
                from_candid_nested_res_n13(result[2])
            ];
        }
    }
    async h(arg0: Array<string | null>, arg1: {
        __kind__: "A";
        A: bigint;
    } | {
        __kind__: "B";
        B: string | null;
    }, arg2: List | null): Promise<{
        _42_: {
        };
        id: bigint;
    }> {
        if (this.processError) {
            try {
                const result = await this.actor.h(to_candid_vec_n17(arg0), to_candid_variant_n19(arg1), to_candid_opt_n9(arg2));
                return result;
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.h(to_candid_vec_n17(arg0), to_candid_variant_n19(arg1), to_candid_opt_n9(arg2));
            return result;
        }
    }
    async i(arg0: List, arg1: [Principal, string]): Promise<[List | null, res]> {
        if (this.processError) {
            try {
                const result = await this.actor.i(to_candid_List_n6(arg0), arg1);
                return [
                    from_candid_opt_n20(result[0]),
                    from_candid_res_n24(result[1])
                ];
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.i(to_candid_List_n6(arg0), arg1);
            return [
                from_candid_opt_n20(result[0]),
                from_candid_res_n24(result[1])
            ];
        }
    }
    async x(arg0: a, arg1: b): Promise<[a | null, b | null, {
            __kind__: "Ok";
            Ok: {
                result: string;
            };
        } | {
            __kind__: "Err";
            Err: Variant_a_b;
        }]> {
        if (this.processError) {
            try {
                const result = await this.actor.x(to_candid_a_n26(arg0), arg1);
                return [
                    from_candid_opt_n28(result[0]),
                    from_candid_opt_n31(result[1]),
                    from_candid_variant_n32(result[2])
                ];
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.x(to_candid_a_n26(arg0), arg1);
            return [
                from_candid_opt_n28(result[0]),
                from_candid_opt_n31(result[1]),
                from_candid_variant_n32(result[2])
            ];
        }
    }
    async y(arg0: nested_records): Promise<[nested_records, my_variant]> {
        if (this.processError) {
            try {
                const result = await this.actor.y(to_candid_nested_records_n34(arg0));
                return from_candid_tuple_n36(result);
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.y(to_candid_nested_records_n34(arg0));
            return from_candid_tuple_n36(result);
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
    async g(arg0: list): Promise<[B, tree, stream]> {
        if (this.processError) {
            try {
                const result = await this.actor.g(to_candid_list_n1(arg0));
                return [
                    from_candid_B_n43(result[0]),
                    from_candid_tree_n46(result[1]),
                    from_candid_stream_n49(result[2])
                ];
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.g(to_candid_list_n1(arg0));
            return [
                from_candid_B_n43(result[0]),
                from_candid_tree_n46(result[1]),
                from_candid_stream_n49(result[2])
            ];
        }
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
}
export const example: exampleInterface = new Example();
function from_candid_A_n45(value: _A): A {
    return from_candid_opt_n44(value);
}
function from_candid_B_n43(value: _B): B {
    return from_candid_opt_n44(value);
}
function from_candid_List_n21(value: _List): List {
    return from_candid_opt_n22(value);
}
function from_candid_a_n29(value: _a): a {
    return from_candid_variant_n30(value);
}
function from_candid_my_variant_n40(value: _my_variant): my_variant {
    return from_candid_variant_n41(value);
}
function from_candid_nested_records_n37(value: _nested_records): nested_records {
    return from_candid_record_n38(value);
}
function from_candid_nested_res_n13(value: _nested_res): nested_res {
    return from_candid_variant_n14(value);
}
function from_candid_opt_n20(value: [] | [_List]): List | null {
    return value.length === 0 ? null : from_candid_List_n21(value[0]);
}
function from_candid_opt_n22(value: [] | [{
        head: bigint;
        tail: _List;
    }]): {
    head: bigint;
    tail: List;
} | null {
    return value.length === 0 ? null : from_candid_record_n23(value[0]);
}
function from_candid_opt_n28(value: [] | [_a]): a | null {
    return value.length === 0 ? null : from_candid_a_n29(value[0]);
}
function from_candid_opt_n31(value: [] | [_b]): b | null {
    return value.length === 0 ? null : value[0];
}
function from_candid_opt_n39(value: [] | [{
        nested_field: string;
    }]): {
    nested_field: string;
} | null {
    return value.length === 0 ? null : value[0];
}
function from_candid_opt_n42(value: [] | [{
        d: string;
        e: Array<{
            f: bigint;
        }>;
    }]): {
    d: string;
    e: Array<{
        f: bigint;
    }>;
} | null {
    return value.length === 0 ? null : value[0];
}
function from_candid_opt_n44(value: [] | [_A]): Some<A> | None {
    return value.length === 0 ? none() : some(from_candid_A_n45(value[0]));
}
function from_candid_opt_n50(value: [] | [{
        head: bigint;
        next: [Principal, string];
    }]): {
    head: bigint;
    next: [Principal, string];
} | null {
    return value.length === 0 ? null : value[0];
}
function from_candid_record_n23(value: {
    head: bigint;
    tail: _List;
}): {
    head: bigint;
    tail: List;
} {
    return {
        head: value.head,
        tail: from_candid_List_n21(value.tail)
    };
}
function from_candid_record_n38(value: {
    nested: [] | [{
            nested_field: string;
        }];
}): {
    nested?: {
        nested_field: string;
    };
} {
    return {
        nested: record_opt_to_undefined(from_candid_opt_n39(value.nested))
    };
}
function from_candid_record_n48(value: {
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
        left: from_candid_tree_n46(value.left),
        right: from_candid_tree_n46(value.right)
    };
}
function from_candid_res_n24(value: _res): res {
    return from_candid_variant_n25(value);
}
function from_candid_stream_n49(value: _stream): stream {
    return from_candid_opt_n50(value);
}
function from_candid_tree_n46(value: _tree): tree {
    return from_candid_variant_n47(value);
}
function from_candid_tuple_n36(value: [_nested_records, _my_variant]): [nested_records, my_variant] {
    return [
        from_candid_nested_records_n37(value[0]),
        from_candid_my_variant_n40(value[1])
    ];
}
function from_candid_variant_n14(value: {
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
    __kind__: "Ok";
    Ok: Variant_Ok_Err;
} | {
    __kind__: "Err";
    Err: {
        __kind__: "Ok";
        Ok: {
            content: string;
        };
    } | {
        __kind__: "Err";
        Err: [bigint];
    };
} {
    return "Ok" in value ? {
        __kind__: "Ok",
        Ok: from_candid_variant_n15(value.Ok)
    } : "Err" in value ? {
        __kind__: "Err",
        Err: from_candid_variant_n16(value.Err)
    } : value;
}
function from_candid_variant_n15(value: {
    Ok: null;
} | {
    Err: null;
}): Variant_Ok_Err {
    return "Ok" in value ? Variant_Ok_Err.Ok : "Err" in value ? Variant_Ok_Err.Err : value;
}
function from_candid_variant_n16(value: {
    Ok: {
        content: string;
    };
} | {
    Err: [bigint];
}): {
    __kind__: "Ok";
    Ok: {
        content: string;
    };
} | {
    __kind__: "Err";
    Err: [bigint];
} {
    return "Ok" in value ? {
        __kind__: "Ok",
        Ok: value.Ok
    } : "Err" in value ? {
        __kind__: "Err",
        Err: value.Err
    } : value;
}
function from_candid_variant_n25(value: {
    Ok: [bigint, bigint];
} | {
    Err: {
        error: string;
    };
}): {
    __kind__: "Ok";
    Ok: [bigint, bigint];
} | {
    __kind__: "Err";
    Err: {
        error: string;
    };
} {
    return "Ok" in value ? {
        __kind__: "Ok",
        Ok: value.Ok
    } : "Err" in value ? {
        __kind__: "Err",
        Err: value.Err
    } : value;
}
function from_candid_variant_n30(value: {
    a: null;
} | {
    b: _b;
}): {
    __kind__: "a";
    a: null;
} | {
    __kind__: "b";
    b: b;
} {
    return "a" in value ? {
        __kind__: "a",
        a: value.a
    } : "b" in value ? {
        __kind__: "b",
        b: value.b
    } : value;
}
function from_candid_variant_n32(value: {
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
    __kind__: "Ok";
    Ok: {
        result: string;
    };
} | {
    __kind__: "Err";
    Err: Variant_a_b;
} {
    return "Ok" in value ? {
        __kind__: "Ok",
        Ok: value.Ok
    } : "Err" in value ? {
        __kind__: "Err",
        Err: from_candid_variant_n33(value.Err)
    } : value;
}
function from_candid_variant_n33(value: {
    a: null;
} | {
    b: null;
}): Variant_a_b {
    return "a" in value ? Variant_a_b.a : "b" in value ? Variant_a_b.b : value;
}
function from_candid_variant_n41(value: {
    a: {
        b: string;
    };
} | {
    c: [] | [{
            d: string;
            e: Array<{
                f: bigint;
            }>;
        }];
}): {
    __kind__: "a";
    a: {
        b: string;
    };
} | {
    __kind__: "c";
    c: {
        d: string;
        e: Array<{
            f: bigint;
        }>;
    } | null;
} {
    return "a" in value ? {
        __kind__: "a",
        a: value.a
    } : "c" in value ? {
        __kind__: "c",
        c: from_candid_opt_n42(value.c)
    } : value;
}
function from_candid_variant_n47(value: {
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
        branch: from_candid_record_n48(value.branch)
    } : "leaf" in value ? {
        __kind__: "leaf",
        leaf: value.leaf
    } : value;
}
function to_candid_List_n6(value: List): _List {
    return to_candid_opt_n7(value);
}
function to_candid_a_n26(value: a): _a {
    return to_candid_variant_n27(value);
}
function to_candid_list_n1(value: list): _list {
    return to_candid_opt_n2(value);
}
function to_candid_nested_n10(value: nested): _nested {
    return to_candid_record_n11(value);
}
function to_candid_nested_records_n34(value: nested_records): _nested_records {
    return to_candid_record_n35(value);
}
function to_candid_node_n3(value: node): _node {
    return to_candid_record_n4(value);
}
function to_candid_opt_n18(value: string | null): [] | [string] {
    return value === null ? candid_none() : candid_some(value);
}
function to_candid_opt_n2(value: node | null): [] | [_node] {
    return value === null ? candid_none() : candid_some(to_candid_node_n3(value));
}
function to_candid_opt_n5(value: boolean | null): [] | [boolean] {
    return value === null ? candid_none() : candid_some(value);
}
function to_candid_opt_n7(value: {
    head: bigint;
    tail: List;
} | null): [] | [{
        head: bigint;
        tail: _List;
    }] {
    return value === null ? candid_none() : candid_some(to_candid_record_n8(value));
}
function to_candid_opt_n9(value: List | null): [] | [_List] {
    return value === null ? candid_none() : candid_some(to_candid_List_n6(value));
}
function to_candid_record_n11(value: {
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
        _41_: to_candid_variant_n12(value._41_),
        _42_: value._42_
    };
}
function to_candid_record_n35(value: {
    nested?: {
        nested_field: string;
    };
}): {
    nested: [] | [{
            nested_field: string;
        }];
} {
    return {
        nested: value.nested ? candid_some(value.nested) : candid_none()
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
function to_candid_record_n8(value: {
    head: bigint;
    tail: List;
}): {
    head: bigint;
    tail: _List;
} {
    return {
        head: value.head,
        tail: to_candid_List_n6(value.tail)
    };
}
function to_candid_variant_n12(value: Variant__42__A_B_C): {
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
function to_candid_variant_n19(value: {
    __kind__: "A";
    A: bigint;
} | {
    __kind__: "B";
    B: string | null;
}): {
    A: bigint;
} | {
    B: [] | [string];
} {
    return value.__kind__ === "A" ? {
        A: value.A
    } : value.__kind__ === "B" ? {
        B: value.B ? candid_some(value.B) : candid_none()
    } : value;
}
function to_candid_variant_n27(value: {
    __kind__: "a";
    a: null;
} | {
    __kind__: "b";
    b: b;
}): {
    a: null;
} | {
    b: _b;
} {
    return value.__kind__ === "a" ? {
        a: value.a
    } : value.__kind__ === "b" ? {
        b: value.b
    } : value;
}
function to_candid_vec_n17(value: Array<string | null>): Array<[] | [string]> {
    return value.map((x)=>to_candid_opt_n18(x));
}

