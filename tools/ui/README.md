# Candid UI

This canister generates a front-end UI for any canister running on the Internet Computer. 

The backend `didjs` is build with the [Rust CDK](https://github.com/dfinity/cdk-rs) and the [Candid](../../rust/) crate to convert did file into JavaScript.
The frontend `ui` fetches the Candid interface from the running canister (currently only canisters built by Motoko expose the Candid interface) and renders the UI based on the interface signature.

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

Open the `ui` canister in a browser and supply the id parameter in the URL to render a specific canister,
e.g., `localhost:8000/?canisterId=ui-canister-id&id=target-canister-id` for local dev, 
or `ui-canister-id.ic0.app/?id=target-canister-id` for the main network.
