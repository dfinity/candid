# @dfinity/didc

A multi-purpose Candid tool for JavaScript projects, including encoding and decoding Candid values. 

## Usage

```javascript
import { getServiceMethods, encode, decode } from "@dfinity/didc";

// The IDL in text format to be used, most canisters expose their IDL through
// the `candid:service` public metadata.
//
// You can fetch the IDL with an agent call or dfx with `dfx canister metadata <canisterId> candid:service`
export const IDL = `
  type StoreNumberInput = record {
    number : nat64;
  };

  service : {
    store_number : (input : StoreNumberInput) -> ();
    get_number : () -> (nat64) query;
  };
`;

// Gets the service methods from the IDL and returns an array of the methods.
//
// Example returned value: ['store_number', 'get_number']
const methods = getServiceMethods(IDL);

// Encodes a candid in text format to a hex representation.
//
// Example returned value: '4449444c016c01c98dea8b0a7801005a00000000000000'
const encoded = encode({
  idl: IDL,
  input: "(record { number=90; })",
  serviceMethod: "store_number",
  targetFormat: "hex",
});

// Decodes a hex representation of a candid value to a text format.
//
// Example returned value: '(90 : nat64)'
const decoded = decode({
  idl: IDL,
  input: "4449444c0001785a00000000000000",
  serviceMethod: "get_number",
  inputFormat: "hex",
  targetFormat: "candid",
});
```
