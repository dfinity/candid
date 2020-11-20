module.exports = {
  bail: false,
  setupFiles: [],
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
