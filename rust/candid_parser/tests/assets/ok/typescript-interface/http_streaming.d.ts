import type { Principal } from "@dfinity/principal";
export interface Some<T> {
    _tag: "Some";
    value: T;
}
export interface None {
    _tag: "None";
}
export type Option<T> = Some<T> | None;
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
import { ActorCallError, type HttpAgentOptions, type ActorConfig, type Agent } from "@dfinity/agent";
export declare interface CreateActorOptions {
    agent?: Agent;
    agentOptions?: HttpAgentOptions;
    actorOptions?: ActorConfig;
}
export declare const createActor: (options?: CreateActorOptions) => Promise<http_streamingInterface>;
export declare const canisterId: string;
export interface http_streamingInterface {
    httpStreamingCallback(token: StreamingToken): Promise<StreamingCallbackHttpResponse>;
    http_request(request: HttpRequest): Promise<HttpResponse>;
    upload(path: string, mimeType: string, chunk: Uint8Array | number[], complete: boolean): Promise<void>;
}

