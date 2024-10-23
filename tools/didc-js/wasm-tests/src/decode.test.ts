import { decode } from "@dfinity/didc";
import { IDL } from "./test.utils";

describe("decode", () => {
  it("decoding returns the method return type decoded value from hex", () => {
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

  it("decoding returns the method arg type decoded value from hex", () => {
    expect(
      decode({
        idl: IDL,
        input: "4449444c016c01c98dea8b0a7801006400000000000000",
        serviceMethod: "store_number",
        inputFormat: "hex",
        targetFormat: "candid",
        useServiceMethodReturnType: false,
      })
    ).toBe("(record { number = 100 : nat64 })");
  });

  it("decoding without the service method can still return the decoded value", () => {
    expect(
      decode({
        idl: IDL,
        input: "4449444c016c01c98dea8b0a7801006400000000000000",
        inputFormat: "hex",
        targetFormat: "candid",
      })
    ).toBe("(record { 2_709_161_673 = 100 : nat64 })");
  });
});
