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

  type InitArgs = record {
    name : text;
  };

  type SomeType = record {
    field1 : text;
    field2 : nat64;
  };

  service : (InitArgs) -> {
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
  withType: { kind: "methodParams", name: "store_number" },
  targetFormat: "hex",
});

// Encodes a specific type - encode values according to a named type
const encoded = encode({
  idl: IDL,
  input: '(record { field1="Hello"; field2=42 })',
  withType: { kind: "type", name: "SomeType" },
  targetFormat: "hex",
});

// Encodes service constructor parameters
const encoded = encode({
  idl: IDL,
  input: '(record { name="MyCanister" })',
  withType: { kind: "serviceParams" },
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

## API Reference

### getServiceMethods(idl: string): string[]

Returns a list of method names available in the service defined in the IDL.

### encode(args: EncodeArgs): string

Encodes Candid text format to hex or blob format.

Parameters:

- `idl`: The Candid IDL to encode against
- `input`: The Candid text value to encode
- `withType` (optional): Type specifier for encoding (discriminated union):
  - `{ kind: "methodParams", name: "method_name" }`: Uses the parameters of the specified method
  - `{ kind: "type", name: "type_name" }`: Uses the specified type
  - `{ kind: "serviceParams" }`: Uses the service constructor parameters
- `targetFormat` (optional): Output format, either 'hex' (default) or 'blob'

### decode(args: DecodeArgs): string

Decodes hex or blob format to Candid text format.

Parameters:

- `idl`: The Candid IDL to decode against
- `input`: The hex or blob value to decode
- `serviceMethod` (optional): Method to use for type information
- `useServiceMethodReturnType` (optional): Whether to use return types (true) or parameter types (false)
- `inputFormat` (optional): Input format, either 'hex' (default) or 'blob'
- `targetFormat` (optional): Output format, only 'candid' is supported currently
