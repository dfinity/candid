use thiserror::Error;

/// Container for all errors that can occur in this crate.
#[derive(Error, Debug, Eq, PartialEq, Clone)]
pub enum LibraryError {
    /// Failed to parse the provided candid idl.
    #[error(r#"Failed to parse the provided candid idl `{reason}`."#)]
    IdlParsingFailed { reason: String },
    /// Service method not found.
    #[error(r#"Service method not found `{method}`."#)]
    IdlMethodNotFound { method: String },
    /// IDL not specified.
    #[error(r#"IDL not specified."#)]
    IdlNotFound,
    /// Type not found.
    #[error(r#"Type not found `{type_name}`."#)]
    TypeNotFound { type_name: String },
    /// Unexpected service parameters.
    #[error(r#"Unexpected service parameters."#)]
    UnexpectedServiceParams,
    /// Failed to parse arguments.
    #[error(r#"Failed to parse arguments `{reason}`."#)]
    IdlArgsParsingFailed { reason: String },
    /// Failed to convert idl args to bytes.
    #[error(r#"Failed to convert idl args to bytes due to `{reason}`."#)]
    IdlArgsToBytesFailed { reason: String },
    /// Failed to convert bytes to idl args.
    #[error(r#"Failed to convert bytes to idl args due to `{reason}`."#)]
    IdlArgsFromBytesFailed { reason: String },
    /// Validation failed due to specific reason.
    #[error(r#"Validation failed due to `{reason}`."#)]
    ValidationError { reason: String },
    /// Hex decoding failed.
    #[error(r#"Hex decoding failed due to `{reason}`."#)]
    HexDecodingFailed { reason: String },
    /// Candid blob decoding failed.
    #[error(r#"Candid blob decoding failed due to `{reason}`."#)]
    CandidBlobDecodingFailed { reason: String },
    /// Mapping error.
    #[error(r#"Mapping error `{reason}`."#)]
    MappingError { reason: String },
}
