# Candid UI

This canister generates a front-end UI for any canister running on the Internet Computer. 

Thi canister `didjs` is built with the [Rust CDK](https://github.com/dfinity/cdk-rs) and the [Candid](../../rust/) crate to convert did file into JavaScript.

It bundles the certified frontend assets and serves them with a cookie compatible with [CanisterEnv](https://js.icp.build/core/v5.3/libs/agent/canister-env/api/interfaces/canisterenv). The CanisterEnv will contain a `CANISTER_ID` value that the frontend can use to call back to the canister.

The frontend fetches the Candid interface from the target canister by looking it up in the metadata under `candid:service` and renders the UI based on the interface signature.

## Q&A

### Why a single canister?
This canister is also meant to be deployed on the local network during local development. It's easier if everything is self contained.

## Build

You need [`icp`](https://cli.internetcomputer.org), `cargo`, `npm`, `wasm-opt` and
`ic-wasm` for building the canister. The frontend is bundled with [Vite](https://vite.dev).

```bash
cd ui/
npm install
icp network start -d   # start a local replica in the background
icp deploy             # build + deploy the didjs canister locally
```

To deploy to mainnet (the `ic` environment), which targets the existing
`a4gq6-oaaaa-aaaab-qaa4q-cai` canister:

```bash
icp deploy -e ic
```

Project configuration lives in `icp.yaml`. Canister id mappings are stored under
`.icp/`: the mainnet mapping (`.icp/data/mappings/ic.ids.json`) is committed, while
local replica state under `.icp/cache/` is ephemeral and git-ignored.

## Usage

Open the canister in a browser and supply the id parameter in the URL to render a specific canister,
e.g., `didjs.local.localhost:8000/?id=target-canister-id` for local dev
