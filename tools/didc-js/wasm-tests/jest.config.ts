import { createJsWithBabelEsmPreset, JestConfigWithTsJest } from "ts-jest";

const jestConfig: JestConfigWithTsJest = {
  ...createJsWithBabelEsmPreset(),
  testEnvironment: "node",
};

export default jestConfig;
