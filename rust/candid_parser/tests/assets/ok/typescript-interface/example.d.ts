import { type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
import type { Principal } from "@dfinity/principal";
export interface Some<T> {
    __kind__: "Some";
    value: T;
}
export interface None {
    __kind__: "None";
}
export type Option<T> = Some<T> | None;
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
export declare const createActor: (canisterId: string | Principal, options?: CreateActorOptions, processError?: (error: unknown) => never) => exampleInterface;
export declare const canisterId: string;
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

