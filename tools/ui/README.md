# Candid UI

This canister generates a front-end UI for any canister running on the Internet Computer. 

The backend `didjs` is build with the [Rust CDK](https://github.com/dfinity/cdk-rs) and the [Candid](../../rust/) crate to convert did file into JavaScript.
The frontend `ui` fetches the Candid interface from the running canister (currently only canisters built by Motoko expose the Candid interface) and renders the UI based on the interface signature.

## Build

You need `dfx`, `cargo`, `npm` and `wasm-opt` for building the canister.

```bash
cd ui/
npm install
dfx start --background
dfx canister create --all
dfx build
dfx canister install --all
```

## Usage

Open the `ui` canister in a browser and supply the id parameter in the URL to render a specific canister,
e.g., `localhost:8000/?canisterId=ui-canister-id&id=target-canister-id` for local dev, 
or `ui-canister-id.ic0.app/?id=target-canister-id` for the main network.
