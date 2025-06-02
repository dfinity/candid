import { encode } from "@dfinity/didc";
import { IDL } from "./test.utils";

describe("encode", () => {
  it("encoding returns the correct hex encoded value from candid into hex", () => {
    expect(
      encode({
        idl: IDL,
        input: "(record { number=90; })",
        withType: { kind: "methodParams", name: "store_number" },
        targetFormat: "hex",
      })
    ).toBe("4449444c016c01c98dea8b0a7801005a00000000000000");
  });

  it("encoding returns the correct hex encoded value from candid into blob", () => {
    expect(
      encode({
        idl: IDL,
        input: "(record { number=90; })",
        withType: { kind: "methodParams", name: "store_number" },
        targetFormat: "blob",
      })
    ).toBe(
      "DIDL\\01l\\01\\c9\\8d\\ea\\8b\\0ax\\01\\00Z\\00\\00\\00\\00\\00\\00\\00"
    );
  });

  it("encoding works with arbitrary types", () => {
    expect(
      encode({
        idl: IDL,
        input: '(record { field1="test"; field2=90; })',
        withType: { kind: "type", name: "CustomInit" },
        targetFormat: "hex",
      })
    ).toBe(
      "4449444c016c02b79cba840871b89cba840878010004746573745a00000000000000"
    );
  });

  it("encoding works with service parameters (null)", () => {
    expect(
      encode({
        idl: IDL,
        input: "(null)",
        withType: { kind: "serviceParams" },
        targetFormat: "hex",
      })
    ).toBe("4449444c026e016c02b79cba840871b89cba840878010000");
  });

  it("encoding works with service parameters (non-null)", () => {
    expect(
      encode({
        idl: IDL,
        input: '(opt record { field1="test"; field2=90; })',
        withType: { kind: "serviceParams" },
        targetFormat: "hex",
      })
    ).toBe(
      "4449444c026e016c02b79cba840871b89cba84087801000104746573745a00000000000000"
    );
  });

  it("encoding throws an error for unknown types", () => {
    const performEncoding = () =>
      encode({
        idl: IDL,
        input: '(record { field1="test"; field2=90; })',
        withType: { kind: "type", name: "UnknownType" },
        targetFormat: "hex",
      });

    expect(performEncoding).toThrow(Error);
    expect(performEncoding).toThrow("Type not found `UnknownType`.");
  });

  it("encoding throws an error for bad values", () => {
    const performEncoding = () =>
      encode({
        idl: IDL,
        input: '(record { field1="test"; unknown_field="bad"; })',
        withType: { kind: "type", name: "CustomInit" },
        targetFormat: "hex",
      });

    expect(performEncoding).toThrow(Error);
    expect(performEncoding).toThrow(/field field2 not found/);
  });

  it("encoding with an invalid service method throws", () => {
    const performEncoding = () =>
      encode({
        idl: IDL,
        input: "(record { number=90; })",
        withType: { kind: "methodParams", name: "unknown_method" },
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
        withType: { kind: "methodParams", name: "store_number" },
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
