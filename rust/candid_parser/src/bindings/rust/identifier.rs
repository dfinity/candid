use pretty::RcDoc;

/// Rust strict and reserved keywords.
///
/// https://doc.rust-lang.org/reference/keywords.html#strict-keywords
///
/// The keywords in [`UNUSABLE_RAW_IDENTIFIERS`] are excluded here.
static KEYWORDS: [&str; 48] = [
    "as", "break", "const", "continue", "else", "enum", "extern", "false", "fn", "for", "if",
    "impl", "in", "let", "loop", "match", "mod", "move", "mut", "pub", "ref", "return", "static",
    "struct", "trait", "true", "type", "unsafe", "use", "where", "while", "async", "await", "dyn",
    "abstract", "become", "box", "do", "final", "macro", "override", "priv", "typeof", "unsized",
    "virtual", "yield", "try", "gen",
];

/// Rust keywords that cannot be raw identifiers, i.e. prepending `r#` is not allowed.
///
/// https://doc.rust-lang.org/reference/identifiers.html#r-ident.syntax
///
/// - The `RAW_IDENTIFIER` definition excludes the following identifiers: `crate`, `self`, `Self`, `super`.
/// - The `RESERVED_RAW_IDENTIFIER` definition also makes `r#_` an invalid raw identifier.
static UNUSABLE_RAW_IDENTIFIERS: [&str; 5] = ["crate", "self", "Self", "super", "_"];

/// The desired case for the identifier w.r.t. Rust naming conventions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum IdentifierCase {
    /// snake_case
    ///
    /// - record field names
    /// - function names
    Snake,

    /// UpperCamelCase
    ///
    /// - enum variant names
    UpperCamel,
}

/// Converts a given string to a valid Rust identifier in the specified case.
///
/// The processing includes:
/// - Validating the identifier to ensure it starts with an ASCII alphabetic character or underscore,
///  and contains only ASCII alphanumeric characters and underscores. If invalid, it is replaced with
///  a sanitized version (`_hash_`).
/// - Converting the identifier to the specified case (snake_case or UpperCamelCase).
/// - Handling Rust keywords by prefixing with `r#` if necessary. (e.g., `type` => `r#type`)
/// - Appending an underscore for identifiers that cannot be raw identifiers. (e.g., `crate` => `crate_`)
///
/// # Returns
///
/// A tuple containing the formatted identifier as `RcDoc` and a boolean indicating whether the identifier was modified.
pub(super) fn to_identifier_case(id: &str, case: IdentifierCase) -> (RcDoc<'_>, bool) {
    if id.is_empty()
        || id.starts_with(|c: char| !c.is_ascii_alphabetic() && c != '_')
        || id.chars().any(|c| !c.is_ascii_alphanumeric() && c != '_')
    {
        (RcDoc::text(format!("_{}_", candid::idl_hash(id))), true)
    } else {
        // above checks ensure the id contains only ASCII alphanumeric and underscores
        let processed = match case {
            IdentifierCase::Snake => to_snake_case(id),
            IdentifierCase::UpperCamel => to_upper_camel_case(id),
        };
        let modified = processed != id;

        if KEYWORDS.contains(&processed.as_str()) {
            (RcDoc::text(format!("r#{}", processed)), modified)
        } else if UNUSABLE_RAW_IDENTIFIERS.contains(&processed.as_str()) {
            (RcDoc::text(format!("{}_", processed)), true)
        } else {
            (RcDoc::text(processed), modified)
        }
    }
}

/// Converts a given string to a valid Rust identifier in snake_case.
///
/// Input string is assumed to contain only ASCII alphanumeric characters and underscores.
///
/// Insert underscores before uppercase letters (if needed) and convert to lowercase.
/// If the uppercase letter is at the start or follows an underscore, do not insert an additional underscore.
fn to_snake_case(s: &str) -> String {
    let mut processed = String::new();
    let mut prev_char_was_underscore = true; // Initialize to true so no '_' is added before the very first character
    for (i, c) in s.chars().enumerate() {
        if c.is_ascii_uppercase() {
            // Check the conditions for inserting an underscore
            // 1. Not the first character (i > 0)
            // 2. The previous character was NOT an underscore
            if i > 0 && !prev_char_was_underscore {
                processed.push('_');
            }
            // Convert to lowercase and append
            processed.push(c.to_ascii_lowercase());
            // Update the state for the next iteration
            prev_char_was_underscore = false; // The char we just added (lowercase) is not an underscore
        } else {
            // Append the character as is (lowercase letter, digit, or underscore)
            processed.push(c);
            // Update the state for the next iteration
            prev_char_was_underscore = c == '_';
        }
    }
    processed
}

/// Converts a given string to a valid Rust identifier in UpperCamelCase (PascalCase).
///
/// Input string is assumed to contain only ASCII alphanumeric characters and underscores.
///
/// Underscores in the middle of the string are removed, and the character following each underscore is capitalized.
/// Leading and trailing underscores are preserved.
fn to_upper_camel_case(s: &str) -> String {
    let mut processed = String::new();
    let mut is_leading_underscores = true;
    let mut consecutive_underscores = 0;
    for (i, c) in s.chars().enumerate() {
        match c {
            '_' => {
                if i == s.len() - 1 {
                    // trailing underscores
                    processed.push_str(&"_".repeat(consecutive_underscores + 1));
                } else {
                    consecutive_underscores += 1;
                }
            }
            c => {
                if is_leading_underscores {
                    // leading underscores
                    processed.push_str(&"_".repeat(consecutive_underscores));
                    consecutive_underscores = 0;
                    is_leading_underscores = false;
                    // capitalize the first non-underscore character
                    processed.push(c.to_ascii_uppercase());
                } else if consecutive_underscores > 0 {
                    // underscores in the middle
                    consecutive_underscores = 0;
                    // capitalize the character following underscores
                    processed.push(c.to_ascii_uppercase());
                } else {
                    processed.push(c);
                }
            }
        }
    }
    processed
}

#[cfg(test)]
mod tests {
    use super::{to_snake_case, to_upper_camel_case};

    #[test]
    fn test_to_snake_case() {
        assert_eq!(to_snake_case("exampleName"), "example_name");
        assert_eq!(to_snake_case("ExampleName"), "example_name");
        assert_eq!(to_snake_case("example_name"), "example_name");
        assert_eq!(to_snake_case("_"), "_");
        assert_eq!(to_snake_case("_A"), "_a");
        assert_eq!(to_snake_case("A_"), "a_");
        assert_eq!(to_snake_case("_A_"), "_a_");
        assert_eq!(to_snake_case("__A__"), "__a__");
        assert_eq!(to_snake_case("__a__"), "__a__");
        assert_eq!(to_snake_case("__A_B__"), "__a_b__");
        assert_eq!(to_snake_case("ABC"), "a_b_c");
        assert_eq!(to_snake_case("amount_e8s"), "amount_e8s");
    }

    #[test]
    fn test_to_upper_camel_case() {
        assert_eq!(to_upper_camel_case("example_name"), "ExampleName");
        assert_eq!(to_upper_camel_case("ExampleName"), "ExampleName");
        assert_eq!(to_upper_camel_case("exampleName"), "ExampleName");
        assert_eq!(to_upper_camel_case("_"), "_");
        assert_eq!(to_upper_camel_case("_A"), "_A");
        assert_eq!(to_upper_camel_case("A_"), "A_");
        assert_eq!(to_upper_camel_case("_A_"), "_A_");
        assert_eq!(to_upper_camel_case("__A__"), "__A__");
        assert_eq!(to_upper_camel_case("__a__"), "__A__");
        assert_eq!(to_upper_camel_case("__A_B__"), "__AB__");
        assert_eq!(to_upper_camel_case("__Aa___B__c__"), "__AaBC__");
    }
}
