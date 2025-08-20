// This is a generated Motoko binding.
// Please use `import service "ic:canister_id"` instead to call canisters on the IC if possible.

module {
  public type StreamingStrategy = {
    #Callback : { token : StreamingToken; callback : StreamingCallback };
  };
  public type HeaderField = (Text, Text);
  public type StreamingCallback = shared query StreamingToken -> async StreamingCallbackHttpResponse;
  public type HttpResponse = {
    body : Blob;
    headers : [HeaderField];
    streaming_strategy : ?StreamingStrategy;
    status_code : Nat16;
  };
  public type StreamingCallbackHttpResponse = {
    token : ?StreamingToken;
    body : Blob;
  };
  public type StreamingToken = { resource : Text; index : Nat };
  public type HttpRequest = {
    url : Text;
    method : Text;
    body : Blob;
    headers : [HeaderField];
  };
  public type Self = actor {
    httpStreamingCallback : shared query (
        token : StreamingToken
      ) -> async StreamingCallbackHttpResponse;
    http_request : shared query (request : HttpRequest) -> async HttpResponse;
    upload : shared (
        path : Text,
        mimeType : Text,
        chunk : Blob,
        complete : Bool,
      ) -> async ();
  }
}
