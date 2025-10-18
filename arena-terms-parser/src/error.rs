//! # Term Parser Error Type
//!
//! This module defines [`TermParserError`], a unified error enum for the term parser
//! pipeline. It aggregates failures from:
//!
//! - **Numeric parsing** (string → integer),
//! - **UTF-8 decoding** (bytes → `String`),
//! - **Operator-table operations**.
//!
//! Conversions from underlying error types are derived with `#[from]`, enabling
//! ergonomic propagation via the `?` operator in functions that return
//! `Result<T, TermParserError>`.

use crate::Value;
use thiserror::Error;

/// Represents all possible errors that can occur within the calculator.
///
/// [`TermParserError`] provides a single error surface for higher-level functions.
/// Each variant wraps a more specific underlying error, and thanks to `#[from]`
/// you can write `?` at call sites without explicit mapping.
///
/// # Typical sources
///
/// - [`TermParserError::ParseInt`]: converting a numeric token’s text to an integer.
/// - [`TermParserError::FromUtf8`]: decoding raw input bytes as UTF-8 text.
/// - [`TermParserError::SymTab`]: interacting with the symbol table.
///
/// # Examples
/// Propagating a parse failure:
/// ```rust
/// # use arena_terms_parser::TermParserError;
/// # fn demo(s: &str) -> Result<i64, TermParserError> {
/// let n: i64 = s.parse()?; // ParseIntError -> TermParserError via #[from]
/// # Ok(n) }
/// ```
///
/// Wrapping a symbol-table error:
/// ```rust
/// # use arena_terms_parser::{TermParserError, SymTabError};
/// let underlying = SymTabError::InvalidIndex { index: 10, len: 3 };
/// let err: TermParserError = underlying.into();
/// assert!(matches!(err, TermParserError::SymTab(_)));
/// ```
#[derive(Debug, Error)]
pub enum TermParserError {
    /// Tried to extract the wrong enum variant from `Value`.
    #[error("invalid value: expected {expected:?}, found {found:?}")]
    InvalidValue {
        /// The variant we expected (e.g. "String", "Bool", ...).
        expected: &'static str,
        /// The original value, so callers can inspect or recover it.
        found: Value,
    },

    #[error("chrono parse error {0:?}")]
    ChronoParse(#[from] chrono::format::ParseError),

    /// An integer literal could not be parsed from its string representation.
    #[error("unable to parse {0:?}")]
    ParseInt(#[from] std::num::ParseIntError),

    /// Failed to decode UTF-8 bytes from input.
    #[error("utf8 error {0:?}")]
    FromUtf8(#[from] std::string::FromUtf8Error),

    /// Failed to decode UTF-8 bytes from input.
    #[error("utf8 error {0:?}")]
    Utf8(#[from] std::str::Utf8Error),

    /// Failed to convert from int.
    #[error("try from int error {0:?}")]
    TryFromInt(#[from] std::num::TryFromIntError),

    /// Failed to parse float.
    #[error("parse float error {0:?}")]
    ParseFloat(#[from] std::num::ParseFloatError),

    /// Term error.
    #[error("term error {0:?}")]
    Term(#[from] arena_terms::TermError),

    #[error("term parser error {0:?}")]
    Other(String),
}

/// Return a `TermParserError` with a formatted message.
///
/// # Example
/// ```rust, ignore
/// bail!("invalid value: {}", val);
/// ```
#[macro_export]
macro_rules! bail {
    ($($arg:tt)*) => {
        return Err(crate::TermParserError::Other(format!($($arg)*)));
    };
}

/// Construct a `TermParserError` with a formatted message.
///
/// # Example
/// ```rust, ignore
/// error!("invalid value: {}", val);
/// ```
#[macro_export]
macro_rules! parser_error {
    ($($arg:tt)*) => {
        Err(crate::TermParserError::Other(format!($($arg)*)));
    };
}
