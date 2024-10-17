import { decode } from "@dfinity/didc";
import { IDL } from "./test.utils";

describe("decode", () => {
  it("decoding returns the correct candid decoded value from hex", () => {
    expect(
      decode({
        idl: IDL,
        input: "4449444c0001785a00000000000000",
        serviceMethod: "get_number",
        inputFormat: "hex",
        targetFormat: "candid",
      })
    ).toBe("(90 : nat64)");
  });

  it("decoding returns the correct json decoded value from hex", () => {
    const result = decode({
      idl: IDL,
      input: "4449444c0001785a00000000000000",
      serviceMethod: "get_number",
      inputFormat: "hex",
      targetFormat: "json",
    });

    expect(result).toBe('"90"');
    expect(JSON.parse(result)).toBe("90");
  });
});
