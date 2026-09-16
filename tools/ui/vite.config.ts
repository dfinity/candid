import { defineConfig } from "vite";
import cssInjectedByJsPlugin from "vite-plugin-css-injected-by-js";

// The `didjs` canister embeds the built frontend directly via
// `include_bytes!("../../dist/didjs/{index.html,index.js,favicon.ico}")`
// (see src/didjs/lib.rs). So the build must emit exactly those three files,
// with stable (un-hashed) names, into `dist/didjs/`:
//   - index.html  (this entry, processed by Vite)
//   - index.js    (single entry chunk; CSS is inlined into it)
//   - favicon.ico (copied verbatim from the `public/` directory)
export default defineConfig({
  // Inline imported CSS into the JS bundle (the canister only serves index.js,
  // not a separate stylesheet) — mirrors the previous webpack `style-loader`.
  plugins: [cssInjectedByJsPlugin()],
  // Some @dfinity packages reference `global`; map it to `globalThis` for the browser.
  define: {
    global: "globalThis",
  },
  build: {
    outDir: "dist/didjs",
    emptyOutDir: true,
    sourcemap: true,
    target: "es2020",
    cssCodeSplit: false,
    rollupOptions: {
      output: {
        entryFileNames: "index.js",
        chunkFileNames: "index.js",
        assetFileNames: "[name][extname]",
        inlineDynamicImports: true,
      },
    },
  },
});
