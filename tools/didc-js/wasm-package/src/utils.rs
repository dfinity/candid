use crate::errors::LibraryError;
use candid::{types::Type, IDLArgs, TypeEnv};
use candid_parser::{check_prog, parse_idl_value, IDLProg};

/// Parse the provided candid idl and return the parsed AST.
pub fn parse_idl_prog(idl: &str) -> Result<IDLProg, LibraryError> {
    match idl.parse::<IDLProg>() {
        Ok(ast) => Ok(ast),
        Err(e) => Err(LibraryError::IdlParsingFailed {
            reason: e.to_string(),
        }),
    }
}

/// Parse the provided candid arguments and return the parsed AST.
pub fn parse_idl_args(args: &str) -> Result<IDLArgs, LibraryError> {
    match candid_parser::parse_idl_args(args) {
        Ok(ast) => Ok(ast),
        Err(e) => Err(LibraryError::IdlArgsParsingFailed {
            reason: e.to_string(),
        }),
    }
}

#[derive(Debug)]
pub struct ParsedIDL {
    pub env: TypeEnv,
    pub actor: Option<Type>,
}

impl ParsedIDL {
    pub fn new(env: TypeEnv, actor: Option<Type>) -> Self {
        Self { env, actor }
    }
}

/// Parse the provided candid idl and return the parsed AST along with the actor type.
pub fn parse_idl(idl: &str) -> Result<ParsedIDL, LibraryError> {
    let mut env = TypeEnv::new();
    let ast = parse_idl_prog(idl)?;

    let actor = check_prog(&mut env, &ast).map_err(|e| LibraryError::ValidationError {
        reason: e.to_string(),
    })?;

    Ok(ParsedIDL::new(env, actor))
}

/// Decode the provided hex input from text to bytes.
pub fn decode_hex(hex_input: &str) -> Result<Vec<u8>, LibraryError> {
    hex::decode(
        hex_input
            .chars()
            .filter(|c| !c.is_whitespace())
            .collect::<String>(),
    )
    .map_err(|e| LibraryError::HexDecodingFailed {
        reason: e.to_string(),
    })
}

/// Decode the provided candid blob text to bytes.
pub fn decode_candid_blob(blob_input: &str) -> Result<Vec<u8>, LibraryError> {
    let blob_input = match blob_input.starts_with("DIDL") {
        true => format!("blob \"{}\"", blob_input),
        false => blob_input.to_string(),
    };

    match parse_idl_value(&blob_input) {
        Ok(candid_parser::IDLValue::Blob(blob)) => Ok(blob),
        Ok(_) => Err(LibraryError::CandidBlobDecodingFailed {
            reason: "Expected a blob value".to_string(),
        }),
        Err(e) => Err(LibraryError::CandidBlobDecodingFailed {
            reason: format!("Could not decode candid blob: {}", e),
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn can_decode_hex_text_value() {
        // Value generated from: didc encode --format hex '(90 : nat64)'
        let hex_input = "4449444c0001785a00000000000000";

        let result = decode_hex(hex_input);

        assert!(result.is_ok());
        assert_eq!(
            result.unwrap(),
            vec![68, 73, 68, 76, 0, 1, 120, 90, 0, 0, 0, 0, 0, 0, 0]
        );
    }

    #[test]
    fn can_decode_candid_blob_text_value() {
        // Value generated from: didc encode --format blob '(90 : nat64)'
        let blob_input = "DIDL\\00\\01xZ\\00\\00\\00\\00\\00\\00\\00";

        let result = decode_candid_blob(blob_input);

        assert!(result.is_ok());
        assert_eq!(
            result.unwrap(),
            vec![68, 73, 68, 76, 0, 1, 120, 90, 0, 0, 0, 0, 0, 0, 0]
        );
    }
}
