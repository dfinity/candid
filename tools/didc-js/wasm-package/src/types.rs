use std::str::FromStr;

use serde::{Deserialize, Serialize};
use wasm_bindgen::JsCast;
use wasm_bindgen::{prelude::wasm_bindgen, JsValue};

use crate::errors::LibraryError;

#[wasm_bindgen(typescript_custom_section)]
const TS_TYPES: &'static str = r#"
export interface EncodeArgs {
  /**
   * The Candid IDL to convert into the candid ast and encode the value against.
   */
  idl: string;
  /**
   * A method to pick from the service. If not provided, the entire idl is used.
   */
  serviceMethod?: string;
  /**
   * The format to encode the value in. Default is 'hex'.
   */
  targetFormat?: 'hex' | 'blob';
  /**
   * The candid text value to encode to the specified format.
   */
  input: string;
}

export interface DecodeArgs {
  /**
   * The Candid IDL to convert into the candid ast and decode the value against.
   */
  idl: string;
  /**
   * The format to decode the value in. Default is 'candid'.
   */
  targetFormat?: 'candid';
  /**
   * A method to pick from the service. If not provided, the entire idl is used.
   */
  serviceMethod?: string;
  /**
   * Wether to use the service method return type to decode the value. Default is true if serviceMethod is provided.
   */
  useServiceMethodReturnType?: boolean;
  /**
   * The format of the input value. Default is 'hex'.
   */
  inputFormat?: 'hex' | 'blob';
  /**
   * The hex or blob value to decode to the specified format.
   */
  input: string;
}
"#;

#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(typescript_type = "EncodeArgs")]
    pub type JsEncodeArgs;

    #[wasm_bindgen(typescript_type = "DecodeArgs")]
    pub type JsDecodeArgs;
}

#[derive(Debug, Serialize, Deserialize)]
pub struct EncodeArgs {
    pub idl: String,
    pub target_format: EncodeFormat,
    pub input: String,
    pub service_method: Option<String>,
}

#[derive(Debug, Serialize, Deserialize, Eq, PartialEq)]
pub enum EncodeFormat {
    Hex,
    Blob,
}

impl FromStr for EncodeFormat {
    type Err = LibraryError;

    fn from_str(variant: &str) -> Result<EncodeFormat, Self::Err> {
        match variant {
            "hex" => Ok(EncodeFormat::Hex),
            "blob" => Ok(EncodeFormat::Blob),
            _ => Err(LibraryError::ValidationError {
                reason: format!("Invalid target format: {}", variant),
            }),
        }
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct DecodeArgs {
    pub idl: String,
    pub target_format: DecodeFormat,
    pub input_format: EncodeFormat,
    pub input: String,
    pub service_method: Option<String>,
    pub use_service_method_return_type: Option<bool>,
}

#[derive(Debug, Serialize, Deserialize, Eq, PartialEq)]
pub enum DecodeFormat {
    Candid,
}

impl FromStr for DecodeFormat {
    type Err = LibraryError;

    fn from_str(variant: &str) -> Result<DecodeFormat, Self::Err> {
        match variant {
            "candid" => Ok(DecodeFormat::Candid),
            _ => Err(LibraryError::ValidationError {
                reason: format!("Invalid target format: {}", variant),
            }),
        }
    }
}

impl TryFrom<JsEncodeArgs> for EncodeArgs {
    type Error = LibraryError;

    fn try_from(args: JsEncodeArgs) -> Result<Self, Self::Error> {
        let js_value = JsValue::from(args);

        let obj =
            js_value
                .dyn_into::<js_sys::Object>()
                .map_err(|_| LibraryError::MappingError {
                    reason: "Could not convert encode arguments".to_string(),
                })?;

        let idl = js_sys::Reflect::get(&obj, &JsValue::from_str("idl"))
            .map_err(|_| LibraryError::MappingError {
                reason: "Could not get 'idl' from JsValue".to_string(),
            })?
            .as_string()
            .ok_or(LibraryError::MappingError {
                reason: "Field 'idl' should be a string".to_string(),
            })?;

        let input = js_sys::Reflect::get(&obj, &JsValue::from_str("input"))
            .map_err(|_| LibraryError::MappingError {
                reason: "Could not get 'input' from JsValue".to_string(),
            })?
            .as_string()
            .ok_or(LibraryError::MappingError {
                reason: "Field 'input' should be a string".to_string(),
            })?;

        let service_method = js_sys::Reflect::get(&obj, &JsValue::from_str("serviceMethod"))
            .map_err(|_| LibraryError::MappingError {
                reason: "Could not get 'serviceMethod' from JsValue".to_string(),
            })?
            .as_string();

        let target_form = js_sys::Reflect::get(&obj, &JsValue::from_str("targetFormat"))
            .map_err(|_| LibraryError::MappingError {
                reason: "Could not get 'targetFormat' from JsValue".to_string(),
            })?
            .as_string();

        let target_format = match target_form {
            Some(target_form) => target_form.parse::<EncodeFormat>()?,
            None => EncodeFormat::Hex,
        };

        Ok(EncodeArgs {
            idl,
            target_format,
            input,
            service_method,
        })
    }
}

impl TryFrom<JsDecodeArgs> for DecodeArgs {
    type Error = LibraryError;

    fn try_from(args: JsDecodeArgs) -> Result<Self, Self::Error> {
        let js_value = JsValue::from(args);

        let obj =
            js_value
                .dyn_into::<js_sys::Object>()
                .map_err(|_| LibraryError::MappingError {
                    reason: "Could not convert decode arguments".to_string(),
                })?;

        let idl = js_sys::Reflect::get(&obj, &JsValue::from_str("idl"))
            .map_err(|_| LibraryError::MappingError {
                reason: "Could not get 'idl' from JsValue".to_string(),
            })?
            .as_string()
            .ok_or(LibraryError::MappingError {
                reason: "Field 'idl' should be a string".to_string(),
            })?;

        let input = js_sys::Reflect::get(&obj, &JsValue::from_str("input"))
            .map_err(|_| LibraryError::MappingError {
                reason: "Could not get 'input' from JsValue".to_string(),
            })?
            .as_string()
            .ok_or(LibraryError::MappingError {
                reason: "Field 'input' should be a string".to_string(),
            })?;

        let service_method = js_sys::Reflect::get(&obj, &JsValue::from_str("serviceMethod"))
            .map_err(|_| LibraryError::MappingError {
                reason: "Could not get 'serviceMethod' from JsValue".to_string(),
            })?
            .as_string();

        let use_service_method_return_type =
            js_sys::Reflect::get(&obj, &JsValue::from_str("useServiceMethodReturnType"))
                .map_err(|_| LibraryError::MappingError {
                    reason: "Could not get 'useServiceMethodReturnType' from JsValue".to_string(),
                })?
                .as_bool();

        let target_form = js_sys::Reflect::get(&obj, &JsValue::from_str("targetFormat"))
            .map_err(|_| LibraryError::MappingError {
                reason: "Could not get 'targetFormat' from JsValue".to_string(),
            })?
            .as_string();

        let target_format = match target_form {
            Some(target_form) => target_form.parse::<DecodeFormat>()?,
            None => DecodeFormat::Candid,
        };

        let input_form = js_sys::Reflect::get(&obj, &JsValue::from_str("inputFormat"))
            .map_err(|_| LibraryError::MappingError {
                reason: "Could not get 'inputFormat' from JsValue".to_string(),
            })?
            .as_string();

        let input_format = match input_form {
            Some(input_form) => input_form.parse::<EncodeFormat>()?,
            None => EncodeFormat::Hex,
        };

        Ok(DecodeArgs {
            idl,
            target_format,
            input_format,
            input,
            service_method,
            use_service_method_return_type,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn can_map_encode_format_enum() {
        let hex = "hex".parse::<EncodeFormat>();
        let blob = "blob".parse::<EncodeFormat>();

        assert!(hex.is_ok());
        assert!(blob.is_ok());
        assert_eq!(hex.unwrap(), EncodeFormat::Hex);
        assert_eq!(blob.unwrap(), EncodeFormat::Blob);
    }

    #[test]
    fn can_map_decode_format_enum() {
        let candid = "candid".parse::<DecodeFormat>();

        assert!(candid.is_ok());
        assert_eq!(candid.unwrap(), DecodeFormat::Candid);
    }

    #[test]
    fn fails_map_unknown_encode_format_enum() {
        let unknown = "unknown".parse::<EncodeFormat>();

        assert!(unknown.is_err());
    }

    #[test]
    fn fails_map_unknown_decode_format_enum() {
        let unknown = "unknown".parse::<DecodeFormat>();

        assert!(unknown.is_err());
    }
}
