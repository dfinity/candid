import { encode } from "@dfinity/didc";
import { IDL } from "./test.utils";

describe("encode", () => {
  it("encoding returns the correct hex encoded value from candid into hex", () => {
    expect(
      encode({
        idl: IDL,
        input: "(record { number=90; })",
        serviceMethod: "store_number",
        targetFormat: "hex",
      })
    ).toBe("4449444c016c01c98dea8b0a7801005a00000000000000");
  });

  it("encoding returns the correct hex encoded value from candid into blob", () => {
    expect(
      encode({
        idl: IDL,
        input: "(record { number=90; })",
        serviceMethod: "store_number",
        targetFormat: "blob",
      })
    ).toBe(
      "DIDL\\01l\\01\\c9\\8d\\ea\\8b\\0ax\\01\\00Z\\00\\00\\00\\00\\00\\00\\00"
    );
  });

  it("encoding with an invalid service method throws", () => {
    const performEncoding = () =>
      encode({
        idl: IDL,
        input: "(record { number=90; })",
        serviceMethod: "unknown_method",
      });

    expect(performEncoding).toThrow(Error);
    expect(performEncoding).toThrow(
      "Service method not found `unknown_method`."
    );
  });

  it("encoding with an invalid input throws", () => {
    const performEncoding = () =>
      encode({
        idl: IDL,
        input: "record { number=90; }",
        serviceMethod: "store_number",
      });

    expect(performEncoding).toThrow(Error);
    expect(performEncoding).toThrow("Failed to parse arguments");
  });

  it("encoding with an invalid IDL throws", () => {
    const performEncoding = () =>
      encode({
        idl: "type StoreNumberInput = number : nat64;",
        input: "(record { number=90; })",
      });

    expect(performEncoding).toThrow(Error);
    expect(performEncoding).toThrow("Failed to parse the provided candid idl");
  });
});
