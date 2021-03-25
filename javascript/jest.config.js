module.exports = {
  bail: false,
  setupFiles: [
    "./test-setup",
  ],
  setupFilesAfterEnv: [
    "jest-expect-message",
  ],
  testPathIgnorePatterns: [
    "/node_modules/",
    "/out/",
  ],
  transform: {
    "^.+\\.ts$": "ts-jest"
  }
};
