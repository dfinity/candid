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
    __kind__: "Callback";
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
export declare const createActor: (canisterId: string | Principal, options?: CreateActorOptions, processError?: (error: unknown) => never) => http_streamingInterface;
export declare const canisterId: string;
export interface http_streamingInterface {
    httpStreamingCallback(token: StreamingToken): Promise<StreamingCallbackHttpResponse>;
    http_request(request: HttpRequest): Promise<HttpResponse>;
    upload(path: string, mimeType: string, chunk: Uint8Array | number[], complete: boolean): Promise<void>;
}

