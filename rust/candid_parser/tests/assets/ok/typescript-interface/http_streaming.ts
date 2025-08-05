import { type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
import { http_streaming as _http_streaming, createActor as _createActor, canisterId as _canisterId } from "declarations/http_streaming";
import { type ActorSubclass } from "@dfinity/agent";
import { _SERVICE } from "declarations/http_streaming/http_streaming.did.d.js";
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
export type HeaderField = [string, string];
export interface HttpRequest {
    url: string;
    method: string;
    body: Uint8Array | number[];
    headers: Array<HeaderField>;
}
export interface HttpResponse {
    body: Uint8Array | number[];
    headers: Array<HeaderField>;
    streaming_strategy?: StreamingStrategy;
    status_code: number;
}
export type StreamingCallback = (arg0: StreamingToken) => Promise<StreamingCallbackHttpResponse>;
export interface StreamingCallbackHttpResponse {
    token?: StreamingToken;
    body: Uint8Array | number[];
}
export type StreamingStrategy = {
    Callback: {
        token: StreamingToken;
        callback: [Principal, string];
    };
};
export interface StreamingToken {
    resource: string;
    index: bigint;
}
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export function createActor(canisterId: string | Principal, options?: CreateActorOptions): http_streamingInterface {
    const actor = _createActor(canisterId, options);
    return new Http_streaming(actor);
}
export const canisterId = _canisterId;
export interface http_streamingInterface {
    httpStreamingCallback(token: StreamingToken): Promise<StreamingCallbackHttpResponse>;
    http_request(request: HttpRequest): Promise<HttpResponse>;
    upload(path: string, mimeType: string, chunk: Uint8Array | number[], complete: boolean): Promise<void>;
}
import type { HeaderField as _HeaderField, HttpResponse as _HttpResponse, StreamingCallbackHttpResponse as _StreamingCallbackHttpResponse, StreamingStrategy as _StreamingStrategy, StreamingToken as _StreamingToken } from "declarations/http_streaming/http_streaming.did.d.ts";
class Http_streaming implements http_streamingInterface {
    private actor: ActorSubclass<_SERVICE>;
    constructor(actor?: ActorSubclass<_SERVICE>, private processError?: (error: unknown) => never){
        this.actor = actor ?? _http_streaming;
    }
    async httpStreamingCallback(arg0: StreamingToken): Promise<StreamingCallbackHttpResponse> {
        if (this.processError) {
            try {
                const result = await this.actor.httpStreamingCallback(arg0);
                return from_candid_StreamingCallbackHttpResponse_n1(result);
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.httpStreamingCallback(arg0);
            return from_candid_StreamingCallbackHttpResponse_n1(result);
        }
    }
    async http_request(arg0: HttpRequest): Promise<HttpResponse> {
        if (this.processError) {
            try {
                const result = await this.actor.http_request(arg0);
                return from_candid_HttpResponse_n4(result);
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.http_request(arg0);
            return from_candid_HttpResponse_n4(result);
        }
    }
    async upload(arg0: string, arg1: string, arg2: Uint8Array | number[], arg3: boolean): Promise<void> {
        if (this.processError) {
            try {
                const result = await this.actor.upload(arg0, arg1, arg2, arg3);
                return result;
            } catch (e) {
                this.processError(e);
                throw new Error("unreachable");
            }
        } else {
            const result = await this.actor.upload(arg0, arg1, arg2, arg3);
            return result;
        }
    }
}
export const http_streaming: http_streamingInterface = new Http_streaming();
function from_candid_HttpResponse_n4(value: _HttpResponse): HttpResponse {
    return from_candid_record_n5(value);
}
function from_candid_StreamingCallbackHttpResponse_n1(value: _StreamingCallbackHttpResponse): StreamingCallbackHttpResponse {
    return from_candid_record_n2(value);
}
function from_candid_StreamingStrategy_n7(value: _StreamingStrategy): StreamingStrategy {
    return from_candid_variant_n8(value);
}
function from_candid_opt_n3(value: [] | [_StreamingToken]): StreamingToken | null {
    return value.length === 0 ? null : value[0];
}
function from_candid_opt_n6(value: [] | [_StreamingStrategy]): StreamingStrategy | null {
    return value.length === 0 ? null : from_candid_StreamingStrategy_n7(value[0]);
}
function from_candid_record_n2(value: {
    token: [] | [_StreamingToken];
    body: Uint8Array | number[];
}): {
    token?: StreamingToken;
    body: Uint8Array | number[];
} {
    return {
        token: record_opt_to_undefined(from_candid_opt_n3(value.token)),
        body: value.body
    };
}
function from_candid_record_n5(value: {
    body: Uint8Array | number[];
    headers: Array<_HeaderField>;
    streaming_strategy: [] | [_StreamingStrategy];
    status_code: number;
}): {
    body: Uint8Array | number[];
    headers: Array<HeaderField>;
    streaming_strategy?: StreamingStrategy;
    status_code: number;
} {
    return {
        body: value.body,
        headers: value.headers,
        streaming_strategy: record_opt_to_undefined(from_candid_opt_n6(value.streaming_strategy)),
        status_code: value.status_code
    };
}
function from_candid_variant_n8(value: {
    Callback: {
        token: _StreamingToken;
        callback: [Principal, string];
    };
}): {
    Callback: {
        token: StreamingToken;
        callback: [Principal, string];
    };
} {
    return "Callback" in value ? {
        Callback: value.Callback
    } : value;
}

