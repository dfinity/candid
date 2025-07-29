use types::{JsDecodeArgs, JsEncodeArgs};
use wasm_bindgen::prelude::*;

mod core;
mod errors;
mod types;
mod utils;
mod validation;

#[wasm_bindgen(start)]
fn start() {
    console_error_panic_hook::set_once();
    match log::set_logger(&wasm_bindgen_console_logger::DEFAULT_LOGGER) {
        Ok(_) => log::info!("Console logger initialized"),
        Err(e) => log::error!("Failed to set console logger: {}", e),
    }
    log::set_max_level(log::LevelFilter::Trace);
}

#[wasm_bindgen(js_name = getServiceMethods)]
pub fn get_service_methods(idl: String) -> Result<Vec<String>, JsError> {
    core::get_service_methods(idl).map_err(Into::into)
}

#[wasm_bindgen]
pub fn encode(args: JsEncodeArgs) -> Result<String, JsError> {
    core::encode(args.try_into()?).map_err(Into::into)
}

#[wasm_bindgen]
pub fn decode(args: JsDecodeArgs) -> Result<String, JsError> {
    core::decode(args.try_into()?).map_err(Into::into)
}
