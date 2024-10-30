import { getServiceMethods } from "@dfinity/didc";
import { IDL, IDL_SERVICE_METHODS } from "./test.utils";

describe("getServiceMethods", () => {
  it("returns the available service methods from an IDL", () => {
    expect(getServiceMethods(IDL)).toEqual(
      expect.arrayContaining(IDL_SERVICE_METHODS)
    );
  });

  it("returns an empty array for a non service IDL", () => {
    expect(getServiceMethods("type TestInput = nat64;")).toEqual([]);
  });
});
