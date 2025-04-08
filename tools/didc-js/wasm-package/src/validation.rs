use crate::{
    errors::LibraryError,
    types::{DecodeArgs, EncodeArgs},
};

/// A trait for validating structs or enums.
///
/// Can be implemented for any struct or enum that needs to be validated.
pub trait Validate<Err = LibraryError> {
    fn validate(&self) -> Result<(), Err>;
}

/// Ensures that the specified field is not empty.
pub fn validate_required_text_field(
    field_name: &str,
    field_value: &str,
) -> Result<(), LibraryError> {
    if field_value.is_empty() || field_value.trim().is_empty() {
        return Err(LibraryError::ValidationError {
            reason: format!("{} is required", field_name),
        });
    }

    Ok(())
}

impl Validate for EncodeArgs {
    fn validate(&self) -> Result<(), LibraryError> {
        validate_required_text_field("idl", &self.idl)?;
        validate_required_text_field("input", &self.input)?;

        Ok(())
    }
}

impl Validate for DecodeArgs {
    fn validate(&self) -> Result<(), LibraryError> {
        validate_required_text_field("idl", &self.idl)?;
        validate_required_text_field("input", &self.input)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{DecodeFormat, EncodeFormat};

    #[test]
    fn test_validate_required_text_field() {
        assert!(validate_required_text_field("test", "test").is_ok());
        assert!(validate_required_text_field("test", "").is_err());
        assert!(validate_required_text_field("test", " ").is_err());
    }

    #[test]
    fn test_validate_encode_args() {
        let args = EncodeArgs {
            idl: "test".to_string(),
            target_format: EncodeFormat::Hex,
            input: "test".to_string(),
            with_type: None,
        };

        assert!(args.validate().is_ok());
    }

    #[test]
    fn test_validate_decode_args() {
        let args = DecodeArgs {
            idl: "test".to_string(),
            target_format: DecodeFormat::Candid,
            input_format: EncodeFormat::Hex,
            input: "test".to_string(),
            service_method: None,
            use_service_method_return_type: None,
        };

        assert!(args.validate().is_ok());
    }
}
