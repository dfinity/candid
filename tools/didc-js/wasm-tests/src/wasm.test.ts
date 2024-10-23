import wasmModule, { encode, decode } from "@dfinity/didc";

describe("WebAssembly nodejs", () => {
  it("the wasm module can be imported", () => {
    expect(wasmModule).not.toBeUndefined();
  });

  it("the wasm module is not a promise", () => {
    expect(wasmModule).not.toBeInstanceOf(Promise);
  });

  it("the encode and decode functions are defined", () => {
    expect(encode).not.toBeUndefined();
    expect(decode).not.toBeUndefined();
  });
});
