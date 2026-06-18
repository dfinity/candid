import { defineConfig } from "vite";
import cssInjectedByJsPlugin from "vite-plugin-css-injected-by-js";
import { icpBindgen } from "@icp-sdk/bindgen/plugins/vite";

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
  plugins: [
    cssInjectedByJsPlugin(),
    // Generate typed bindings for the fixed ic-wasm profiler interface
    // (`__get_cycles` / `__get_profiling`) from src/profiler.did.
    icpBindgen({
      didFile: "./src/profiler.did",
      outDir: "./src/bindings/profiler",
    }),
    // Generate typed bindings for the didjs canister's own interface
    // (`did_to_js` etc.) from its candid definition. The high-level actor
    // wrapper is disabled because the `subtype` method has a parameter named
    // `new` (a JS reserved word) that the wrapper can't represent; we use the
    // low-level idlFactory + _SERVICE from the declarations instead.
    icpBindgen({
      didFile: "./src/didjs/didjs.did",
      outDir: "./src/bindings/didjs",
      output: { actor: { disabled: true } },
    }),
  ],
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
