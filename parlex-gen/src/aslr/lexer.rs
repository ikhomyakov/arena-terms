//! Lexer module.
//!
//! This module defines the lexer used for tokenizing grammar source files into
//! structured [`Token`]s. It serves as the first stage of the compilation or
//! parser generation pipeline, converting raw text into lexical units that are
//! later consumed by the [`parser`](crate::parser) module.
//!
//! # Overview
//! The lexer is built on top of the [`logos`] crate and uses a declarative
//! token specification (`LogosToken`) to identify terminals, nonterminals,
//! production labels, and punctuation. It also includes symbol mapping utilities
//! and context tracking via [`LexContext`].
//!
//! # Components
//! - [`Lexer`]: Core lexer implementation that wraps a [`logos::Lexer`].
//! - [`LexContext`]: Maintains symbol tables and shared state during lexing.
//! - [`Token`]: Represents all token kinds recognized by the lexer.
//! - [`SYM_NAMES`]: Static table mapping symbol characters (e.g., `'+'`, `'('`) to
//!   canonical human-readable names.
//!
//! # See Also
//! - [`crate::parser`]: For grammar parsing built on top of lexer output.
//! - [`logos`]: External crate providing the lexer engine.
//!
//! # Notes
//! - Whitespace and comments are skipped automatically by the [`LogosToken`] definition.
//! - The lexer ensures deterministic tokenization suitable for grammar analysis.
use super::symtab::Symtab;
use logos::Logos;
use std::collections::HashMap;

/// Holds symbol tables used during grammar lexing and parsing.
///
/// `LexContext` tracks terminals, nonterminals, and production labels
/// encountered in a grammar specification. It is used internally by
/// the grammar parser and lexer generators to build consistent symbol mappings.
///
/// # Fields
/// - `terms`: Table of terminal symbols.
/// - `nonterms`: Table of nonterminal symbols.
/// - `prod_labels`: Table of production rule labels.
#[derive(Default, Debug)]
pub struct LexContext {
    /// Symbol table of terminal symbols.
    pub terms: Symtab,

    /// Symbol table of nonterminal symbols.
    pub nonterms: Symtab,

    /// Symbol table of production labels.
    pub prod_labels: Symtab,
}

/// Tokens produced by the grammar lexer.
///
/// Represents syntactic elements encountered in grammar definitions,
/// such as terminals, nonterminals, and production separators (`->`).
#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    /// A production label (e.g., `Expr1:`).
    ProdLabel(usize),

    /// A nonterminal symbol (e.g., `Expr`).
    NonTerm(usize),

    /// A production separator (`->`).
    Prod,

    /// A terminal symbol (e.g., `PLUS`, `'+'`).
    Term(usize),

    /// A line feed (`\n`), marking rule boundaries.
    LineFeed,
}

/// Raw tokens recognized by the `logos`-based lexer.
///
/// Used internally by the grammar lexer to tokenize grammar source files.
/// Skips whitespace and distinguishes between labels, symbols, and comments.
#[derive(Logos, Debug, PartialEq)]
#[logos(skip r"[ \t\f]+")]
enum LogosToken {
    /// Line break (`\n`), typically marking the end of a production rule.
    #[regex(r"[\n]")]
    LineFeed,

    /// A comment line beginning with `--`, ignored during parsing.
    #[regex(r"--[^\n]*")]
    Comment,

    /// The production separator symbol (`->`).
    #[regex(r"->")]
    Prod,

    /// A production label (e.g., `Expr1:`).
    #[regex(r"[a-z]([a-zA-Z0-9])*:")]
    ProdLabel,

    /// An atom or lowercase identifier representing a terminal (e.g., `expr`, `value`).
    #[regex(r"[a-z]([a-zA-Z0-9])*")]
    Atom,

    /// An uppercase identifier representing a non-termminal (e.g., `ID`, `PLUS`).
    #[regex(r"[A-Z][a-zA-Z0-9]*")]
    Var,

    /// A symbolic punctuation or operator (e.g., `+`, `;`, `(`, `)`).
    #[regex(r###"[-~`!@#$%^&*+=|\\<>?/;\(\)\[\]{},\.'":]"###)]
    Sym,
}

/// Mapping of symbolic characters to human-readable names.
///
/// Used during lexer and parser code generation to assign descriptive
/// identifiers to punctuation and operator symbols. This allows symbols
/// such as `'+'` or `'('` to be referenced as `plus` or `leftParen` in
/// generated Rust code.
///
/// # Notes
/// - Each entry is a `(char, &str)` pair.
/// - The string names follow camel-case conventions (e.g., `"leftParen"`, `"greaterThan"`).
pub const SYM_NAMES: &[(char, &str)] = &[
    ('.', "dot"),
    ('-', "minus"),
    ('~', "tilde"),
    ('`', "backtick"),
    ('!', "exclamation"),
    ('@', "at"),
    ('#', "hash"),
    ('$', "dollar"),
    ('%', "percent"),
    ('^', "caret"),
    ('&', "ampersand"),
    ('*', "asterisk"),
    ('+', "plus"),
    ('=', "equals"),
    ('|', "pipe"),
    ('\\', "backslash"),
    ('<', "lessThan"),
    ('>', "greaterThan"),
    ('?', "question"),
    ('/', "slash"),
    (';', "semicolon"),
    ('(', "leftParen"),
    (')', "rightParen"),
    ('[', "leftBrack"),
    (']', "rightBrack"),
    ('{', "leftBrace"),
    ('}', "rightBrace"),
    (',', "comma"),
    ('\'', "singleQuote"),
    ('"', "doubleQuote"),
    (':', "colon"),
];

/// Source-level lexer for grammar files.
///
/// The `Lexer` wraps a [`logos::Lexer`] instance over a source string
/// and produces [`Token`]s for parser or compiler front-end consumption.
/// It performs symbol name mapping, token classification, and basic
/// lexical filtering (e.g., whitespace and comments).
///
/// # Lifetimes
/// - `'source`: The lifetime of the input source string being tokenized.
pub struct Lexer<'source> {
    /// The underlying [`logos::Lexer`] instance that performs token recognition
    /// using the [`LogosToken`] enum definition.
    ///
    /// This lexer drives the low-level tokenization of the source input.
    inner: logos::Lexer<'source, LogosToken>,

    /// Mapping of symbol characters (e.g., `+`, `(`, `>`) to their
    /// canonical human-readable names.
    ///
    /// Derived from the static [`SYM_NAMES`] table, this map provides
    /// consistent symbolic identifiers during lexing and code generation.
    sym_names: HashMap<char, &'static str>,
}

/// Implementation of [`Lexer`] methods.
///
/// This `impl` provides construction and tokenization logic for the grammar lexer.
/// It defines methods to initialize a new lexer, iterate through tokens, and
/// process the full input into a token stream.
///
/// # Type Parameters
/// - `'source`: The lifetime of the input string being lexed.
///
/// # Overview
/// The [`Lexer`] wraps a [`logos::Lexer`] to perform token recognition over
/// grammar specifications. It leverages the [`SYM_NAMES`] table for
/// symbol normalization and updates a shared [`LexContext`] during parsing.
impl<'source> Lexer<'source> {
    /// Creates a new [`Lexer`] from the provided source input.
    ///
    /// Initializes the internal [`logos::Lexer`] and populates the
    /// symbol name lookup table from [`SYM_NAMES`].
    ///
    /// # Parameters
    /// - `input`: The source string to tokenize.
    pub fn new(input: &'source str) -> Self {
        Self {
            inner: LogosToken::lexer(input),
            sym_names: SYM_NAMES.iter().cloned().collect(),
        }
    }

    /// Retrieves the next token from the input stream, if available.
    ///
    /// Consumes the next recognized token, updates the provided
    /// [`LexContext`], and returns a corresponding [`Token`] variant.
    ///
    /// Returns `None` when the input is fully consumed.
    ///
    /// # Parameters
    /// - `ctx`: Mutable reference to the [`LexContext`] tracking
    ///   symbol and nonterminal tables.
    ///
    /// # Returns
    /// The next [`Token`] or `None` at end of input.
    pub fn next_token(&mut self, ctx: &mut LexContext) -> Option<Token> {
        while let Some(kind) = self.inner.next() {
            let slice = self.inner.slice();
            return match kind {
                Ok(token) => match token {
                    LogosToken::Sym => {
                        let name = if let Some(first_char) = slice.chars().next() {
                            if let Some(name) = self.sym_names.get(&first_char) {
                                name
                            } else {
                                unreachable!();
                            }
                        } else {
                            unreachable!();
                        };
                        Some(Token::Term(ctx.terms.add(name)))
                    }
                    LogosToken::Atom => Some(Token::Term(ctx.terms.add(slice))),
                    LogosToken::Var => Some(Token::NonTerm(ctx.nonterms.add(slice))),
                    LogosToken::ProdLabel => {
                        let slice = match slice.char_indices().next_back() {
                            Some((idx, _)) => &slice[..idx],
                            None => "",
                        };
                        Some(Token::ProdLabel(ctx.prod_labels.add(slice)))
                    }
                    LogosToken::Prod => Some(Token::Prod),
                    LogosToken::Comment => continue,
                    LogosToken::LineFeed => Some(Token::LineFeed),
                },
                Err(err) => {
                    panic!("Lexer error: {err:?}");
                }
            };
        }
        None
    }

    /// Tokenizes the entire input into a sequence of [`Token`]s.
    ///
    /// Repeatedly calls [`Lexer::next_token`] until the input stream
    /// is exhausted, returning all recognized tokens in order.
    ///
    /// # Parameters
    /// - `input`: The source text to lex.
    /// - `ctx`: Mutable reference to the [`LexContext`] shared across tokens.
    ///
    /// # Returns
    /// A vector of all recognized tokens from the input.
    pub fn tokenize_all(input: &'source str, ctx: &mut LexContext) -> Vec<Token> {
        let mut lex = Lexer::new(input);
        let mut out = Vec::new();
        while let Some(tok) = lex.next_token(ctx) {
            out.push(tok);
        }
        out
    }
}

/// Unit tests for the [`Lexer`] implementation.
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_terms() {
        let mut ctx = LexContext::default();
        let input = "\n\n\nfoo: XYZ -> +& () bar x123 ABC -- hello\n";
        let toks = Lexer::tokenize_all(input, &mut ctx);
        assert!(toks.len() == 14);
    }
}
