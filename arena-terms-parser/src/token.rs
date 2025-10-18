//! # Term Parser Tokens
//!
//! Concrete token value and token type used by the parser pipeline.
//!
//! Provides:
//! - [`Value`]: the payload carried by lexical tokens (e.g., arena term or index),
//! - [`TermToken`]: a concrete token implementation that pairs a [`TokenID`],
//!   a [`Value`], and a source line number, implementing [`parlex::Token`].
//!
//! These are produced by the lexer and consumed by the parser and later stages.

use crate::{TermParserError, TokenID};
use arena_terms::Term;
use parlex::Token;

/// Represents a generic value emitted by the lexer.
///
/// `Value` encapsulates auxiliary data produced during lexing, such as parsed
/// terms or indices into the parser's term stack.
///
/// # Variants
/// - [`Value::None`] — Indicates absence of a value.
/// - [`Value::Term`] — Wraps a parsed [`Term`] instance.
/// - [`Value::Index`] — Holds a numeric index.
#[derive(Debug, Clone, Copy, Default)]
pub enum Value {
    #[default]
    None,
    Term(Term),
    Index(usize),
}

/// Macro that implements [`TryFrom<Value>`] for selected target types.
///
/// Converts from a generic [`Value`] into concrete types such as [`Term`]
/// or `usize`. If the variant does not match, returns an error.
macro_rules! impl_tryfrom_value {
    ( $( $Variant:ident => $ty:ty ),+ $(,)? ) => {
        $(
            impl ::core::convert::TryFrom<Value> for $ty {
                type Error = TermParserError;
                fn try_from(v: Value) -> Result<Self, TermParserError> {
                    match v {
                        Value::$Variant(x) => Ok(x),
                        other => Err(TermParserError::InvalidValue {
                            expected: stringify!($Variant),
                            found: other,
                        }),
                    }
                }
            }
        )+
    };
}

// Implements TryFrom<Value> for Term and usize.
impl_tryfrom_value! {
    Term => Term,
    Index => usize,
}

// Implements TryFrom<Value> for Option<Term>
impl TryFrom<Value> for Option<Term> {
    type Error = TermParserError;
    fn try_from(v: Value) -> Result<Self, TermParserError> {
        match v {
            Value::None => Ok(None),
            Value::Term(x) => Ok(Some(x)),
            other => Err(TermParserError::InvalidValue {
                expected: "Term or None",
                found: other,
            }),
        }
    }
}

/// A token produced by the [`TermLexer`] for Prolog-like term parsing.
///
/// Each [`TermToken`] encapsulates:
/// - the syntactic token kind (`token_id`),
/// - an associated semantic [`Value`],
/// - the line number on which it was recognized, and
/// - an optional operator-table index used for precedence/associativity lookup.
#[derive(Debug, Clone)]
pub struct TermToken {
    ///
    pub token_id: TokenID,
    /// The associated value (if any).
    pub value: Value,
    /// The line number where the token was recognized.
    pub line_no: usize,
    /// Optional operator definition index.
    pub op_tab_index: Option<usize>,
}

impl TermToken {
    /// Creates a new [`TermToken`] with the specified token ID, value, and line number.
    ///
    /// # Parameters
    /// - `token_id`: Token identifier from the lexer’s token table.
    /// - `value`: Optional value attached to the token.
    /// - `line_no`: Source line number where this token was found.
    ///
    /// The `op_tab_index` field is initialized to `None` by default.
    #[must_use]
    pub fn new(token_id: TokenID, value: Value, line_no: usize) -> Self {
        Self {
            token_id,
            value,
            line_no,
            op_tab_index: None,
        }
    }
}

/// Implements the [`Token`] trait for [`TermToken`], allowing integration
/// with the `parlex` core library.
impl Token for TermToken {
    type TokenID = TokenID;

    fn token_id(&self) -> Self::TokenID {
        self.token_id
    }
    fn line_no(&self) -> usize {
        self.line_no
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::convert::TryFrom;

    #[test]
    fn try_from_value_to_usize_success() {
        let v = Value::Index(42);
        let got = usize::try_from(v).expect("Index -> usize should succeed");
        assert_eq!(got, 42);
    }

    #[test]
    fn try_from_value_to_usize_wrong_variant_err() {
        // Using Value::None to avoid depending on Term
        let v = Value::None;
        let err = usize::try_from(v).expect_err("None -> usize must error");
        let msg = format!("{err:#}");
        // Should mention we expected Index and say what we actually got
        assert!(msg.contains("expected Index"), "msg={msg}");
        assert!(msg.contains("None"), "msg={msg}");
    }

    #[test]
    fn try_from_value_to_option_term_none_success() {
        let v = Value::None;
        let got = <Option<Term>>::try_from(v).expect("None -> Option<Term> should succeed");
        assert!(got.is_none());
    }

    #[test]
    fn try_from_value_to_option_term_wrong_variant_err() {
        let v = Value::Index(7);
        let err = <Option<Term>>::try_from(v).expect_err("Index -> Option<Term> must error");
        let msg = format!("{err:#}");
        // Message from the impl should be clear
        assert!(msg.contains("expected Term or None"), "msg={msg}");
    }

    #[test]
    fn roundtrip_index_via_value() {
        let input = 123usize;
        let got = usize::try_from(Value::Index(input)).unwrap();
        assert_eq!(got, input);
    }
}
