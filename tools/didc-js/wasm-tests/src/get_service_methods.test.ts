import { get_service_methods } from "@dfinity/didc";
import { IDL, IDL_SERVICE_METHODS } from "./test.utils";

describe("get_service_methods", () => {
  it("returns the available service methods from an IDL", () => {
    expect(get_service_methods(IDL)).toEqual(
      expect.arrayContaining(IDL_SERVICE_METHODS)
    );
  });

  it("returns an empty array for a non service IDL", () => {
    expect(get_service_methods("type TestInput = nat64;")).toEqual([]);
  });
});
