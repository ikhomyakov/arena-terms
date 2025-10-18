//! Defines [`TermError`], the unified error type for term operations.
//!
//! Provides descriptive error variants for invalid terms, epochs,
//! kind or arity mismatches, and related arena issues.

use crate::{EpochID, Slice, Term};
use smartstring::alias::String;
use thiserror::Error;

/// Represents all possible errors that can occur within the calculator.
///
/// [`TermError`] provides a single error surface for higher-level functions.
/// Each variant wraps a more specific underlying error, and thanks to `#[from]`
/// you can write `?` at call sites without explicit mapping.
///

#[derive(Debug, Clone, Error)]
pub enum TermError {
    #[error("Invalid term {0:?}")]
    InvalidTerm(Term),

    #[error("Epoch overflow")]
    LiveEpochsExceeded,

    #[error("Invalid epoch {0:?}")]
    InvalidEpoch(EpochID),

    #[error("Missing functor")]
    MissingFunctor,

    #[error("Invalid functor {0:?}")]
    InvalidFunctor(Term),

    #[error("Type mismatch: expected {expected}, found {found}")]
    UnexpectedKind {
        expected: &'static str,
        found: &'static str,
    },

    #[error("Arity mismatch: expected {expected}, found {found}")]
    UnexpectedArity { expected: usize, found: usize },

    #[error("Unexpected name in {0:?}")]
    UnexpectedName(Term),

    // OperDef fixity errors
    #[error("invalid fixity: {0}")]
    InvalidFixity(String),

    // OperDef associativity errors
    #[error("invalid associativity: {0}")]
    InvalidAssoc(String),

    // An   OperDef error
    #[error("operdef error: {0}")]
    OperDef(String),
}

/// Internal errors that may occur when constructing terms or
/// interacting with arena.
#[derive(Debug, Clone, Error)]
pub(crate) enum InternalTermError {
    /// Invalid arena epoch ID.
    #[error("invalid arena epoch: {0:?}")]
    InvalidEpoch(EpochID),

    /// Invalid slice.
    #[error("invalid term slice: {0:?}")]
    InvalidSlice(Slice),
}
