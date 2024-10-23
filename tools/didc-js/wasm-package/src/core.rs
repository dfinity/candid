use crate::validation::Validate;
use candid::IDLArgs;

use crate::{
    errors::LibraryError,
    types::{DecodeArgs, DecodeFormat, EncodeArgs, EncodeFormat},
    utils::{decode_candid_blob, decode_hex, parse_idl, parse_idl_args},
};

pub fn get_service_methods(idl: String) -> Result<Vec<String>, LibraryError> {
    let idl = parse_idl(&idl)?;
    let mut methods = Vec::new();

    if let Some(actor) = &idl.actor {
        let service = idl
            .env
            .as_service(actor)
            .map_err(|e| LibraryError::IdlParsingFailed {
                reason: format!("Could not convert to service {}", e),
            })?;

        for (method_name, _) in service.iter() {
            methods.push(method_name.clone());
        }
    }

    methods.sort();

    Ok(methods)
}

/// Encode the provided input in candid text format to the specified format.
pub fn encode(args: EncodeArgs) -> Result<String, LibraryError> {
    // Validate the provided arguments
    args.validate()?;

    let idl = parse_idl(&args.idl)?;
    let idl_args = parse_idl_args(&args.input)?;

    let args_bytes = match (args.service_method, &idl.actor) {
        (Some(method), Some(actor)) => {
            let method = idl.env.get_method(actor, &method).map_err(|_| {
                LibraryError::IdlMethodNotFound {
                    method: method.clone(),
                }
            })?;

            idl_args
                .to_bytes_with_types(&idl.env, &method.args)
                .map_err(|e| LibraryError::IdlArgsToBytesFailed {
                    reason: format!("Could not encode args to bytes {}", e),
                })?
        }
        (Some(method), None) => Err(LibraryError::IdlMethodNotFound { method })?,
        (None, _) => idl_args
            .to_bytes()
            .map_err(|e| LibraryError::IdlArgsToBytesFailed {
                reason: format!("Could not encode args to bytes {}", e),
            })?,
    };

    let encoded_args = match args.target_format {
        EncodeFormat::Hex => hex::encode(&args_bytes),
        EncodeFormat::Blob => {
            let mut res = String::new();
            for ch in args_bytes.iter() {
                res.push_str(&candid_parser::pretty::candid::value::pp_char(*ch));
            }

            res
        }
    };

    Ok(encoded_args)
}

/// Decode the provided hex or blob value to the specified format.
pub fn decode(args: DecodeArgs) -> Result<String, LibraryError> {
    // Validate the provided arguments
    args.validate()?;

    let idl = parse_idl(&args.idl)?;
    let args_bytes = match args.input_format {
        EncodeFormat::Hex => decode_hex(&args.input)?,
        EncodeFormat::Blob => decode_candid_blob(&args.input)?,
    };

    let idl_args = match (args.service_method, &idl.actor) {
        (Some(method), Some(actor)) => {
            let method = idl.env.get_method(actor, &method).map_err(|_| {
                LibraryError::IdlMethodNotFound {
                    method: method.clone(),
                }
            })?;

            let method_types = match args.use_service_method_return_type {
                None | Some(true) => &method.rets,
                Some(false) => &method.args,
            };

            IDLArgs::from_bytes_with_types(&args_bytes, &idl.env, method_types).map_err(|e| {
                LibraryError::IdlArgsFromBytesFailed {
                    reason: format!("Could not decode args from bytes {}", e),
                }
            })?
        }
        (Some(method), None) => Err(LibraryError::IdlMethodNotFound { method })?,
        (None, _) => {
            IDLArgs::from_bytes(&args_bytes).map_err(|e| LibraryError::IdlArgsFromBytesFailed {
                reason: format!("Could not decode args from bytes {}", e),
            })?
        }
    };

    let decoded_idl_args = match args.target_format {
        DecodeFormat::Candid => idl_args.to_string(),
    };

    Ok(decoded_idl_args)
}
