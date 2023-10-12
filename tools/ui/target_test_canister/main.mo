import Principal "mo:base/Principal";
import Error "mo:base/Error";
import Text "mo:base/Text";
import { responseBody } "./AlternativeOrigin";

actor {
    // Only this principal is allowed to call the `hello` method.
    // Anyone can change this principal by calling the `_set_allowed_principal` method 
    // to test the login flow.
    var allowed = Principal.fromText("oigup-gpnce-ytl3m-gkuwt-hf4yc-lci5d-ijsy5-oc4ak-kz3v2-fjbl5-mae");

    public func _set_allowed_principal(principal : Text) : async () {
        allowed := Principal.fromText(principal);
    };

    public query func _get_allowed_principal() : async Text {
        Principal.toText(allowed);
    };

    public shared query ({ caller }) func hello() : async Text {
        if (caller != allowed) {
            throw Error.reject("Unauthorized");
        };

        "Hello World!";
    };

    // Both the `http_request` (query) and `http_request_update` (update) methods
    // are implemented to 'upgrade to update' so that `/.well-known/ii-alternative-origins`
    // response can be verified 
    // See https://internetcomputer.org/docs/current/references/ii-spec#alternative-frontend-origins
    type HttpRequest = {
        method : Text;
        url : Text;
        headers : [(Text, Text)];
        body : Blob;
        certificate_version : ?Nat16;
    };

    type HttpResponse = {
        status_code : Nat16;
        headers : [(Text, Text)];
        body : Blob;
        upgrade : ?Bool;
    };

    public query func http_request(req : HttpRequest) : async HttpResponse {
        {
            status_code = 200;
            headers = [];
            upgrade = ?true;
            body = Text.encodeUtf8("");
        };
    };

    public func http_request_update(req : HttpRequest) : async HttpResponse {
        if (req.url == "/.well-known/ii-alternative-origins") {
            return {
                status_code = 200;
                headers = [("Access-Control-Allow-Origin", "https://identity.ic0.app")];
                body = responseBody();
                upgrade = ?false;
            };
        } else {
            throw Error.reject("Not found");
        };
    };
};
