import Principal "mo:base/Principal";
import Error "mo:base/Error";
import Text "mo:base/Text";
import Blob "mo:base/Blob";

actor {
    let owner = Principal.fromText("oigup-gpnce-ytl3m-gkuwt-hf4yc-lci5d-ijsy5-oc4ak-kz3v2-fjbl5-mae");

    public shared query ({ caller }) func hello() : async Text {
        if (caller != owner) {
            throw Error.reject("Unauthorized");
        };

        "Hello World!";
    };

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
                body = Text.encodeUtf8(
                    "{
  \"alternativeOrigins\": [
    \"https://m4ul7-aqaaa-aaaal-qcewq-cai.raw.icp0.io\"
  ]
}"
                );
                upgrade = ?false;
            };
        } else {
            throw Error.reject("Not found");
        };
    };
};
