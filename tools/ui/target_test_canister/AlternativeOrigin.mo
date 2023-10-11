import Text "mo:base/Text";

module {
    // This should be the domain at which the Candid UI canister is serving its frontend
    // Candid UI canister id in production is `https://a4gq6-oaaaa-aaaab-qaa4q-cai.raw.icp0.io`
    // Using A test version of the Candid UI canister here
    let ALTERNATIVE_ORIGIN : Text = "https://m4ul7-aqaaa-aaaal-qcewq-cai.raw.icp0.io";

    public func responseBody() : Blob {
        let body = "{ \"alternativeOrigins\": [\"" # ALTERNATIVE_ORIGIN # "\"] }";
        Text.encodeUtf8(body);
    };
};
