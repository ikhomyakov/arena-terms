//! Parser for Prolog-like terms with operator definitions.
//!
//! This module defines the [`TermParser`], which implements a shift-reduce SLR(1) parser
//! for Prolog-style terms tokenized by the [`TermLexer`]. It integrates with operator
//! definitions ([`OperDefs`]) to correctly resolve shift/reduce conflicts according to declared
//! precedence and associativity rules.
//!             
//! The parser consumes tokens produced by [`TermLexer`] and uses a mutable
//! [`Arena`] as shared context to construct arena-allocated [`Term`] values
//! (from the [`arena_terms`] crate) representing atoms, numbers, compound terms,
//! lists, tuples, and other structures.
//!
//! Generated parsing tables and rules are produced by **parlex-gen**’s [`aslr`] tool.
//!
//! [`TermParser`]: struct.TermParser
//! [`TermLexer`]: crate::lexer::TermLexer
//! [`TermToken`]: crate::lexer::TermToken
//! [`OperDefs`]: crate::oper::OperDefs
//! [`arena_terms`]: https://crates.io/crates/arena-terms
//! [`aslr`]: https://crates.io/crates/parlex-gen

use crate::{TermLexer, TermToken, TokenID, Value};
use arena_terms::{Arena, Assoc, Fixity, MAX_OPER_PREC, MIN_OPER_PREC, Term, View};
use parlex::{
    LexerStats, ParlexError, Parser, ParserAction, ParserData, ParserDriver, ParserStats, Token,
};
use parser_data::{AmbigID, ParData, ProdID, StateID};
use std::marker::PhantomData;
use try_next::TryNextWithContext;

/// Includes the generated SLR parser tables and definitions.
///         
/// This file (`parser_data.rs`) is produced by the **parlex-gen** [`aslr`] tool
/// during the build process. It defines the parsing automaton, rule metadata,
/// and associated enum types used by the [`TermParser`].
pub mod parser_data {
    include!(concat!(env!("OUT_DIR"), "/parser_data.rs"));
}

/// A driver that defines semantic actions for the term parser.
///
/// The [`TermParserDriver`] type implements [`ParserDriver`] and acts as the
/// bridge between the parser engine ([`Parser`]) and calculator-specific
/// semantic logic.
///
/// It provides the behavior for grammar reductions and ambiguity resolution
/// during parsing. Each reduction corresponds to a grammar production rule
/// in [`ParData`], and is responsible for building a term.
///
/// # Type Parameters
///
/// - `I`: The input source (the lexer) that yields [`TermToken`]s. Must implement
///   [`TryNextWithContext<Arena, Item = TermToken>`].
///
/// # Associated Types
///
/// - `ParserData = ParData`:
///   Generated parser metadata containing grammar rules, production IDs,
///   and ambiguity identifiers.
/// - `Token = TermToken`:
///   The token type produced by the lexer and consumed by this parser.
/// - `Parser = Parser<I, Self, Arena>`:
///   The parser engine parameterized by this driver and context.
/// - `Error = TermParserError`:
///   Unified error type propagated during parsing.
/// - `Context = Arena`:
///   Externally supplied context.
///
/// # Responsibilities
///
/// The parser driver performs calculator-specific actions:
///
/// - **`resolve_ambiguity`** — invoked when the grammar allows multiple valid
///   interpretations of a token sequence. The driver chooses which parse path
///   to follow by returning an appropriate [`ParserAction`].
/// - **`reduce`** — executed when a grammar production completes. The driver
///   can perform semantic actions such as arithmetic evaluation, updating the
///   symbol table, or producing intermediate values.
pub struct TermParserDriver<I> {
    /// Marker to associate the driver with its input type `I`.
    _marker: PhantomData<I>,

    /// Stack of intermediate [`Term`] values used for reduction of term sequences.
    ///
    /// [`Value::Index`] refers to an entry in this stack, enabling grammar
    /// actions to compose and reduce sequences of terms into higher-level
    /// structures during parsing.
    terms: Vec<Term>,
}

impl<I> ParserDriver for TermParserDriver<I>
where
    I: TryNextWithContext<Arena, LexerStats, Item = TermToken, Error: std::fmt::Display + 'static>,
{
    /// Parser metadata generated from the calculator grammar.
    type ParserData = ParData;

    /// Token type consumed by the parser.
    type Token = TermToken;

    /// Concrete parser engine type.
    type Parser = Parser<I, Self, Self::Context>;

    /// Context (symbol table or shared state).
    type Context = Arena;

    /// Resolves an ambiguity reported by the parser (e.g., shift/reduce).
    ///
    /// Given an ambiguity identifier and the lookahead token `tok2`, this method
    /// chooses the appropriate parser action (shift or reduce) according to the
    /// operator precedence and associativity rules.
    ///
    /// # Parameters
    /// - `_arena`: Arena used to allocate or inspect terms.
    /// - `ambig`:  The generated ambiguity ID (`AmbigID`).
    /// - `tok2`:   The lookahead token at the ambiguity point.
    ///
    /// # Returns
    /// The selected parser [`Action`] to disambiguate the current state.
    ///
    /// # Errors
    /// Returns an error if the ambiguity cannot be resolved consistently.
    ///
    /// # Notes
    /// This grammar contains only **Shift/Reduce** conflicts — cases where
    /// the parser can either:
    /// - **Reduce** using a completed production rule, or
    /// - **Shift** the next incoming token (`tok2`).
    ///
    /// Other types of conflicts (such as **Reduce/Reduce**) are much more
    /// difficult to handle programmatically and usually require modifying
    /// the grammar itself to eliminate ambiguity.
    fn resolve_ambiguity(
        &mut self,
        parser: &mut Self::Parser,
        arena: &mut Self::Context,
        ambig: <Self::ParserData as ParserData>::AmbigID,
        tok2: &Self::Token,
    ) -> Result<ParserAction<StateID, ProdID, AmbigID>, ParlexError> {
        let ambigs = ParData::lookup_ambig(ambig);
        let shift_action = ambigs[0];
        let ParserAction::Shift(_) = shift_action else {
            panic!("expected shift");
        };
        let reduce_action = ambigs[1];
        let ParserAction::Reduce(prod_id) = reduce_action else {
            panic!("expected reduce");
        };

        log::trace!(
            "Conflict between reducing {:?} and shifting {:?}",
            prod_id,
            tok2
        );

        let (fixity1, tok1) = match prod_id {
            ProdID::Infix1 => {
                // Expr -> Expr atomOper Expr
                (Fixity::Infix, parser.tokens_peek(1))
            }
            ProdID::Infix2 => {
                // Expr -> Expr funcOper Seq ) Expr
                (Fixity::Infix, parser.tokens_peek(3))
            }
            ProdID::Prefix1 => {
                // Expr -> atomOper Expr
                (Fixity::Prefix, parser.tokens_peek(1))
            }
            ProdID::Prefix2 => {
                // Expr -> funcOper Seq ) Expr
                (Fixity::Prefix, parser.tokens_peek(3))
            }
            ProdID::Postfix1 => {
                // Expr -> Expr atomOper
                (Fixity::Postfix, parser.tokens_peek(0))
            }
            ProdID::Postfix2 => {
                // Expr -> Expr funcOper Seq )
                (Fixity::Postfix, parser.tokens_peek(2))
            }
            _ => {
                return Err(ParlexError {
                    message: format!(
                        "unexpected conflict: reduction of {:?} with shifting token {:?}",
                        prod_id, tok2
                    ),
                    span: tok2.span(),
                });
            }
        };

        let op_tab1 = arena.get_oper(tok1.op_tab_index);
        let op_tab2 = arena.get_oper(tok2.op_tab_index);

        assert!(op_tab1.is_oper());

        if op_tab2.is_oper() {
            let op_def1 = match op_tab1[fixity1] {
                Some(ref op_def1) => op_def1,
                None => return Ok(shift_action),
            };

            let prec1 = op_def1.prec;
            let assoc1 = op_def1.assoc;

            let min_prec2 = std::cmp::min(
                op_tab2[Fixity::Infix]
                    .as_ref()
                    .map(|x| x.prec)
                    .unwrap_or(MAX_OPER_PREC),
                op_tab2[Fixity::Postfix]
                    .as_ref()
                    .map(|x| x.prec)
                    .unwrap_or(MAX_OPER_PREC),
            );
            let max_prec2 = std::cmp::max(
                op_tab2[Fixity::Infix]
                    .as_ref()
                    .map(|x| x.prec)
                    .unwrap_or(MIN_OPER_PREC),
                op_tab2[Fixity::Postfix]
                    .as_ref()
                    .map(|x| x.prec)
                    .unwrap_or(MIN_OPER_PREC),
            );

            if prec1 > min_prec2 {
                Ok(reduce_action)
            } else if prec1 < max_prec2 {
                Ok(shift_action)
            } else if min_prec2 == max_prec2 && prec1 == min_prec2 {
                if assoc1 == Assoc::None {
                    return Err(ParlexError {
                        message: format!(
                            "precedence conflict: cannot chain non-associative operator {:?}; use parenthesis",
                            tok1
                        ),
                        span: tok2.span(),
                    });
                }
                if op_tab2[Fixity::Infix]
                    .as_ref()
                    .is_some_and(|x| x.assoc == Assoc::None)
                    || op_tab2[Fixity::Postfix]
                        .as_ref()
                        .is_some_and(|x| x.assoc == Assoc::None)
                {
                    return Err(ParlexError {
                        message: format!(
                            "precedence conflict: cannot chain non-associative operator {:?}; use parenthesis",
                            tok2
                        ),
                        span: tok2.span(),
                    });
                }
                if op_tab2[Fixity::Infix]
                    .as_ref()
                    .is_some_and(|x| x.assoc != assoc1)
                    || op_tab2[Fixity::Postfix]
                        .as_ref()
                        .is_some_and(|x| x.assoc != assoc1)
                {
                    return Err(ParlexError {
                        message: format!(
                            "associativity conflict: cannot chain operators {:?} and {:?}; use parenthesis",
                            tok1, tok2
                        ),
                        span: tok2.span(),
                    });
                } else {
                    if assoc1 == Assoc::Left {
                        Ok(reduce_action)
                    } else {
                        Ok(shift_action)
                    }
                }
            } else {
                return Err(ParlexError {
                    message: format!(
                        "precedence conflict: cannot chain operators {:?} and {:?}; use parenthesis",
                        tok1, tok2
                    ),
                    span: tok2.span(),
                });
            }
        } else {
            Ok(shift_action)
        }
    }

    /// Performs a grammar reduction for the given production rule.
    ///
    /// Applies the semantic action for `prod_id`, typically constructing or
    /// normalizing an arena-backed [`Term`], and pushes the resulting token
    /// onto the parser’s value stack.
    ///
    /// # Parameters
    /// - `arena`: Arena used to allocate or inspect terms.
    /// - `prod_id`:  The production being reduced (`ProdID`).
    /// - `token`: The lookahead token (normally not used).
    ///
    /// # Errors
    /// Returns an error if the reduction fails due to arity mismatches,
    /// invalid operator metadata, or inconsistent stack state.
    fn reduce(
        &mut self,
        parser: &mut Self::Parser,
        arena: &mut Self::Context,
        prod_id: <Self::ParserData as ParserData>::ProdID,
        token: &Self::Token,
    ) -> Result<(), ParlexError> {
        match prod_id {
            ProdID::Start => {
                // Accept - does not get reduced
                unreachable!()
            }

            ProdID::Term1 => {
                // Term -> Expr
                let mut expr_tok = parser.tokens_pop();
                expr_tok.token_id = TokenID::Term;
                parser.tokens_push(expr_tok);
            }

            ProdID::Term2 => {
                // Term -> Expr .
                parser.tokens_pop();
                let mut expr_tok = parser.tokens_pop();
                expr_tok.token_id = TokenID::Term;
                parser.tokens_push(expr_tok);
            }

            ProdID::Term3 => {
                // Term ->
                parser.tokens_push(TermToken::new(TokenID::Term, Value::None, token.span()));
            }

            ProdID::Term4 => {
                // Term -> .
                parser.tokens_pop();
                parser.tokens_push(TermToken::new(TokenID::Term, Value::None, token.span()));
            }

            ProdID::Func => {
                // Expr -> func Seq )
                parser.tokens_pop();
                let index = usize::try_from(parser.tokens_pop().value)?;
                let func_tok = parser.tokens_pop();
                let span = func_tok.span();
                let op_tab_index = func_tok.op_tab_index;
                let functor = Term::try_from(func_tok.value)?;

                let vs = std::iter::once(&functor).chain(self.terms[index..].iter());
                let term = arena
                    .funcv(vs)
                    .map_err(|e| ParlexError::from_err(e, span))?;
                self.terms.truncate(index);

                let term = arena
                    .normalize_term(term, Fixity::Fun, op_tab_index)
                    .map_err(|e| ParlexError::from_err(e, span))?;

                parser.tokens_push(TermToken::new(TokenID::Expr, Value::Term(term), span));
            }

            ProdID::List => {
                // Expr -> [ Seq ]
                parser.tokens_pop();
                let seq_tok = parser.tokens_pop();
                let left_brack_tok = parser.tokens_pop();
                let index = usize::try_from(seq_tok.value)?;

                let term = arena.list(&self.terms[index..]);
                self.terms.truncate(index);

                parser.tokens_push(TermToken::new(
                    TokenID::Expr,
                    Value::Term(term),
                    left_brack_tok.span(),
                ));
            }

            ProdID::Nil => {
                // Expr -> [ ]
                parser.tokens_pop();
                let left_brack_tok = parser.tokens_pop();
                parser.tokens_push(TermToken::new(
                    TokenID::Expr,
                    Value::Term(Term::NIL),
                    left_brack_tok.span(),
                ));
            }

            ProdID::List2 => {
                // Expr -> [ Seq | Expr ]
                parser.tokens_pop();
                let tail = Term::try_from(parser.tokens_pop().value)?;
                parser.tokens_pop();
                let index = usize::try_from(parser.tokens_pop().value)?;
                let left_brack_tok = parser.tokens_pop();

                let term = arena.listc(&self.terms[index..], tail);
                self.terms.truncate(index);

                parser.tokens_push(TermToken::new(
                    TokenID::Expr,
                    Value::Term(term),
                    left_brack_tok.span(),
                ));
            }

            ProdID::Tuple => {
                // Expr -> ( Seq )
                parser.tokens_pop();
                let seq_tok = parser.tokens_pop();
                let left_paren_tok = parser.tokens_pop();

                let index = usize::try_from(seq_tok.value)?;

                // Arena terms parser does not currently support unary tuples.
                // TODO: Consider adding explicit unary tuple syntax `(expr,)`.
                let vs = &self.terms[index..];
                let term = if vs.len() == 1 {
                    vs[0]
                } else {
                    arena.tuple(vs)
                };
                self.terms.truncate(index);

                parser.tokens_push(TermToken::new(
                    TokenID::Expr,
                    Value::Term(term),
                    left_paren_tok.span(),
                ));
            }

            ProdID::Unit => {
                // Expr -> ( )
                parser.tokens_pop();
                let left_paren_tok = parser.tokens_pop();
                parser.tokens_push(TermToken::new(
                    TokenID::Expr,
                    Value::Term(Term::UNIT),
                    left_paren_tok.span(),
                ));
            }

            ProdID::Var | ProdID::Int | ProdID::Real | ProdID::Date | ProdID::Str | ProdID::Bin => {
                // Expr -> xxx
                let mut tok = parser.tokens_pop();
                tok.token_id = TokenID::Expr;
                parser.tokens_push(tok);
            }

            ProdID::Atom => {
                // Expr -> atom
                let atom_tok = parser.tokens_pop();
                let span = atom_tok.span();
                let op_tab_index = atom_tok.op_tab_index;

                let atom = Term::try_from(atom_tok.value)?;

                let term = arena
                    .normalize_term(atom, Fixity::Fun, op_tab_index)
                    .map_err(|e| ParlexError::from_err(e, span))?;

                parser.tokens_push(TermToken::new(TokenID::Expr, Value::Term(term), span));
            }

            ProdID::Infix1 => {
                // Expr -> Expr atomOper Expr
                let expr2_tok = parser.tokens_pop();
                let oper_tok = parser.tokens_pop();
                let expr1_tok = parser.tokens_pop();
                let span = expr1_tok.span();
                let op_tab_index = oper_tok.op_tab_index;

                let expr2 = Term::try_from(expr2_tok.value)?;
                let oper = Term::try_from(oper_tok.value)?;
                let expr1 = Term::try_from(expr1_tok.value)?;

                let term = arena
                    .funcv([oper, expr1, expr2])
                    .map_err(|e| ParlexError::from_err(e, span))?;
                let term = arena
                    .normalize_term(term, Fixity::Infix, op_tab_index)
                    .map_err(|e| ParlexError::from_err(e, span))?;

                parser.tokens_push(TermToken::new(TokenID::Expr, Value::Term(term), span));
            }

            ProdID::Infix2 => {
                // Expr -> Expr func Seq ) Expr
                let expr2_tok = parser.tokens_pop();
                parser.tokens_pop();
                let index = usize::try_from(parser.tokens_pop().value)?;
                let oper_tok = parser.tokens_pop();
                let expr1_tok = parser.tokens_pop();
                let span = expr1_tok.span();
                let op_tab_index = oper_tok.op_tab_index;

                let expr2 = Term::try_from(expr2_tok.value)?;
                let oper = Term::try_from(oper_tok.value)?;
                let expr1 = Term::try_from(expr1_tok.value)?;

                let xs = [oper, expr1, expr2];
                let vs = xs.iter().chain(self.terms[index..].iter());
                let term = arena
                    .funcv(vs)
                    .map_err(|e| ParlexError::from_err(e, span))?;
                self.terms.truncate(index);

                let term = arena
                    .normalize_term(term, Fixity::Infix, op_tab_index)
                    .map_err(|e| ParlexError::from_err(e, span))?;

                parser.tokens_push(TermToken::new(TokenID::Expr, Value::Term(term), span));
            }

            ProdID::Prefix1 => {
                // Expr -> atom Expr
                let expr1_tok = parser.tokens_pop();
                let oper_tok = parser.tokens_pop();
                let span = oper_tok.span();
                let op_tab_index = oper_tok.op_tab_index;

                let expr1 = Term::try_from(expr1_tok.value)?;
                let oper = Term::try_from(oper_tok.value)?;

                let term = match oper
                    .view(arena)
                    .map_err(|e| ParlexError::from_err(e, span))?
                {
                    // Arena terms parser currently gives special treatment to unary minus
                    // on integer and real literals (it directly negates them).
                    // TODO: Consider handling minus at the lexical level.
                    View::Atom(s)
                        if s == "-"
                            && matches!(
                                expr1
                                    .view(arena)
                                    .map_err(|e| ParlexError::from_err(e, span))?,
                                View::Int(_) | View::Real(_)
                            ) =>
                    {
                        match expr1
                            .view(arena)
                            .map_err(|e| ParlexError::from_err(e, span))?
                        {
                            View::Int(i) => arena.int(-i),
                            View::Real(r) => arena.real(-r),
                            _ => unreachable!(),
                        }
                    }
                    _ => {
                        let term = arena
                            .funcv([oper, expr1])
                            .map_err(|e| ParlexError::from_err(e, span))?;
                        arena
                            .normalize_term(term, Fixity::Prefix, op_tab_index)
                            .map_err(|e| ParlexError::from_err(e, span))?
                    }
                };

                parser.tokens_push(TermToken::new(TokenID::Expr, Value::Term(term), span));
            }

            ProdID::Prefix2 => {
                // Expr -> func Seq ) Expr
                let expr1_tok = parser.tokens_pop();
                parser.tokens_pop();
                let index = usize::try_from(parser.tokens_pop().value)?;
                let oper_tok = parser.tokens_pop();
                let span = oper_tok.span();
                let op_tab_index = oper_tok.op_tab_index;

                let oper = Term::try_from(oper_tok.value)?;
                let expr1 = Term::try_from(expr1_tok.value)?;

                let xs = [oper, expr1];
                let vs = xs.iter().chain(self.terms[index..].iter());
                let term = arena
                    .funcv(vs)
                    .map_err(|e| ParlexError::from_err(e, span))?;
                self.terms.truncate(index);

                let term = arena
                    .normalize_term(term, Fixity::Prefix, op_tab_index)
                    .map_err(|e| ParlexError::from_err(e, span))?;

                parser.tokens_push(TermToken::new(TokenID::Expr, Value::Term(term), span));
            }

            ProdID::Postfix1 => {
                // Expr -> Expr atomOper
                let oper_tok = parser.tokens_pop();
                let expr1_tok = parser.tokens_pop();
                let span = expr1_tok.span();
                let op_tab_index = oper_tok.op_tab_index;

                let oper = Term::try_from(oper_tok.value)?;
                let expr1 = Term::try_from(expr1_tok.value)?;

                let term = arena
                    .funcv([oper, expr1])
                    .map_err(|e| ParlexError::from_err(e, span))?;
                let term = arena
                    .normalize_term(term, Fixity::Postfix, op_tab_index)
                    .map_err(|e| ParlexError::from_err(e, span))?;

                parser.tokens_push(TermToken::new(TokenID::Expr, Value::Term(term), span));
            }

            ProdID::Postfix2 => {
                // Expr -> Expr func Seq )
                parser.tokens_pop();
                let index = usize::try_from(parser.tokens_pop().value)?;
                let oper_tok = parser.tokens_pop();
                let expr1_tok = parser.tokens_pop();
                let span = expr1_tok.span();
                let op_tab_index = oper_tok.op_tab_index;

                let oper = Term::try_from(oper_tok.value)?;
                let expr1 = Term::try_from(expr1_tok.value)?;

                let xs = [oper, expr1];
                let vs = xs.iter().chain(self.terms[index..].iter());
                let term = arena
                    .funcv(vs)
                    .map_err(|e| ParlexError::from_err(e, span))?;
                self.terms.truncate(index);

                let term = arena
                    .normalize_term(term, Fixity::Postfix, op_tab_index)
                    .map_err(|e| ParlexError::from_err(e, span))?;

                parser.tokens_push(TermToken::new(TokenID::Expr, Value::Term(term), span));
            }

            ProdID::Seq1 => {
                // Seq -> BareSeq
                let mut bare_seq_tok = parser.tokens_pop();
                bare_seq_tok.token_id = TokenID::Seq;
                parser.tokens_push(bare_seq_tok);
            }

            ProdID::Seq2 => {
                // Seq -> BareSeq ,
                parser.tokens_pop();
                let mut bare_seq_tok = parser.tokens_pop();
                bare_seq_tok.token_id = TokenID::Seq;
                parser.tokens_push(bare_seq_tok);
            }

            ProdID::BareSeq1 => {
                // BareSeq -> Expr
                let expr_tok = parser.tokens_pop();
                let span = expr_tok.span();
                let expr = Term::try_from(expr_tok.value)?;

                let index = self.terms.len();
                self.terms.push(expr);

                parser.tokens_push(TermToken::new(TokenID::BareSeq, Value::Index(index), span));
            }

            ProdID::BareSeq2 => {
                // BareSeq -> BareSeq , Expr
                let expr_tok = parser.tokens_pop();
                let expr = Term::try_from(expr_tok.value)?;
                parser.tokens_pop();

                self.terms.push(expr);
            }
        }
        Ok(())
    }
}

/// Prolog-like term parser with operator precedence and associativity handling.
///
/// The [`TermParser0`] drives the parsing of Prolog-style terms using the
/// [`parlex`] SLR(1) core library. It builds upon the [`TermLexer`] for tokenization
/// and produces [`Term`] values stored in an [`Arena`] for efficient allocation.
///
/// Operator definitions are resolved dynamically through an [`OperDefs`] table,
/// allowing user-defined or default operators to control how expressions are
/// grouped and nested according to their **fixity**, **precedence**, and
/// **associativity**.
///
/// /// # Input / Output
///
/// - **Input**: any byte stream `I` implementing
///   [`TryNextWithContext<Arena, Item = u8, Error: std::fmt::Display + 'static>`].
/// - **Output**: completed parsing units as [`TermToken`] values.
///
/// # End Tokens and Multiple Sentences
///
/// The underlying lexer typically emits an explicit [`TokenID::End`] token at
/// the end of a *parsing unit* (end of “sentence” or expression). The parser
/// uses this to finalize and emit one result. If the input contains multiple
/// independent sentences, you will receive multiple results — one per `End` —
/// and `None` only after all input is consumed.
///
/// # Empty Statements
///
/// The terms grammar also accepts an *empty* term, which is returned
/// as a token with [`Value::None`].
/// This occurs, for example, when the last statement in the input is terminated
/// by a semicolon (`.`) but followed by no further expression. In that case:
///
/// 1. The parser first emits the token for the preceding completed term.
/// 2. It then emits an additional token representing the *empty* term
///    (`Value::None`).
/// 3. Finally, it returns `None`, indicating the end of the input stream.
///
/// This design allows the parser to fully reflect the structure of the input.
///
/// # Errors
///
/// All failures are surfaced through a composed
/// [`ParserError<LexerError<I::Error, CalcError>, CalcError, CalcToken>`]:
/// - `I::Error` — errors from the input source,
/// - [`TermParserError`] — lexical/semantic errors (e.g., UTF-8, integer parsing,
///   symbol-table issues).
///
/// # Example
///
/// ```rust
/// # use arena_terms_parser::{TermToken, TermParser0, TokenID, Value};
/// # use arena_terms::Arena;
/// # use try_next::{IterInput, TryNextWithContext};
/// let mut arena = Arena::new();
/// arena.define_default_opers().unwrap();
/// let input = IterInput::from("hello = 1 .\n foo =\n [5, 3, 2].\n (world, hello, 10).\n\n1000".bytes());
/// let mut parser = TermParser0::try_new(input).unwrap();
/// let vs = parser.try_collect_with_context(&mut arena).unwrap();
/// assert_eq!(vs.len(), 4);
/// ```
///
/// [`Arena`]: arena_terms::Arena
/// [`Term`]: arena_terms::Term
/// [`OperDefs`]: crate::OperDefs
/// [`TermLexer`]: crate::TermLexer
/// [`TermToken`]: crate::TermToken
pub struct TermParser0<I>
where
    I: TryNextWithContext<Arena, Item = u8, Error: std::fmt::Display + 'static>,
{
    parser: Parser<TermLexer<I>, TermParserDriver<TermLexer<I>>, Arena>,
}

impl<I> TermParser0<I>
where
    I: TryNextWithContext<Arena, Item = u8, Error: std::fmt::Display + 'static>,
{
    /// Creates a new [`TermParser0`] for the given input stream and operator definitions.
    ///
    /// # Parameters
    /// - `input`: A fused iterator over bytes to be parsed.
    /// - `arena`: A term arena, used to initialized default operator defs.
    ///
    /// # Returns
    /// A fully initialized [`TermParser`] ready to parse Prolog-like terms.
    ///
    /// # Errors
    /// Returns an error if the lexer context cannot be initialized
    /// or if the generated parser tables fail to load.
    pub fn try_new(input: I) -> Result<Self, ParlexError> {
        let lexer = TermLexer::try_new(input)?;
        let driver = TermParserDriver {
            _marker: PhantomData,
            terms: Vec::new(),
        };
        let parser = Parser::new(lexer, driver);
        Ok(Self { parser })
    }

    /// Defines or extends operator definitions directly from a Prolog-like
    /// `op/6` term list read from a separate input source.
    ///
    /// This allows dynamic addition of new operator fixities and precedence
    /// rules during parsing.
    ///
    /// # Parameters
    /// - `arena`: Arena allocator used for constructing term structures.
    /// - `defs_input`: Input byte iterator yielding the operator definition terms.
    /// - `opers`: Optional initial operator table to extend.
    ///   If `None`, the default operator definitions are used.
    ///
    /// # Errors
    /// Returns an error if parsing the operator term list fails or produces
    /// an invalid operator specification.
    pub fn define_opers(arena: &mut Arena, defs_input: I) -> Result<(), ParlexError> {
        let mut defs_parser = TermParser0::try_new(defs_input)?;
        while let Some(TermToken { value, .. }) = defs_parser.try_next_with_context(arena)? {
            //log::trace!("Stats: {:?}", defs_parser.stats(),);
            match value {
                Value::Term(term) => arena
                    .define_opers(term)
                    .map_err(|e| ParlexError::from_err(e, None))?,
                Value::None => continue,
                Value::Index(_) => {
                    return Err(ParlexError {
                        message: format!("index token not expected"),
                        span: None,
                    });
                }
            }
        }
        Ok(())
    }
}

impl<I> TryNextWithContext<Arena, (LexerStats, ParserStats)> for TermParser0<I>
where
    I: TryNextWithContext<Arena, Item = u8, Error: std::fmt::Display + 'static>,
{
    /// Tokens produced by this lexer.
    type Item = TermToken;

    /// Unified error type.
    type Error = ParlexError;

    /// Advances the parser and returns the next token, or `None` at end of input.
    ///
    /// The provided `context` (an [`Arena`]) may be mutated by rule
    /// actions (for example, to intern terms). This method is fallible;
    /// both input and lexical errors are converted into [`Self::Error`].
    ///
    /// # End of Input
    ///
    /// When the lexer reaches the end of the input stream, it will typically
    /// emit a final [`TokenID::End`] token before returning `None`.
    ///
    /// This explicit *End* token is expected by the **Parlex parser** to
    /// signal successful termination of a complete parsing unit.
    /// Consumers should treat this token as a logical *end-of-sentence* or
    /// *end-of-expression* marker, depending on the grammar.
    ///
    /// If the input contains **multiple independent sentences or expressions**,
    /// the lexer may emit multiple `End` tokens—one after each completed unit.
    /// In such cases, the parser can restart or resume parsing after each `End`
    /// to produce multiple parse results from a single input stream.
    ///
    /// Once all input has been consumed, the lexer returns `None`.
    fn try_next_with_context(
        &mut self,
        context: &mut Arena,
    ) -> Result<Option<TermToken>, ParlexError> {
        self.parser.try_next_with_context(context)
    }

    fn stats(&self) -> (LexerStats, ParserStats) {
        self.parser.stats()
    }
}

/// Prolog-like term parser with operator precedence and associativity handling.
///
/// The [`TermParser`] drives the parsing of Prolog-style terms using the
/// [`parlex`] SLR(1) core library. It builds upon the [`TermParser0`] for tokenization
/// and produces [`Term`] values stored in an [`Arena`] for efficient allocation.
///
/// Operator definitions are resolved dynamically through an [`OperDefs`] table,
/// allowing user-defined or default operators to control how expressions are
/// grouped and nested according to their **fixity**, **precedence**, and
/// **associativity**.
///
/// /// # Input / Output
///
/// - **Input**: any byte stream `I` implementing
///   [`TryNextWithContext<Arena, Item = u8>`].
/// - **Output**: completed parsing units as [`TermToken`] values.
///
/// # End Tokens and Multiple Sentences
///
/// The underlying parser  emits an explicit tokens at
/// the end of a *parsing unit* (end of “sentence” or expression). The parser
/// uses this to finalize and emit one result. If the input contains multiple
/// independent sentences, you will receive multiple results — one per `End` —
/// and `None` only after all input is consumed.
///
/// # Empty Statements
///
/// The terms grammar also accepts an *empty* term, which is returned
/// as a token with [`Value::None`].
/// This occurs, for example, when the last statement in the input is terminated
/// by a semicolon (`.`) but followed by no further expression. In that case:
///
/// 1. The parser first emits the token for the preceding completed term.
/// 2. It then emits an additional token representing the *empty* term
///    (`Value::None`).
/// 3. Finally, it returns `None`, indicating the end of the input stream.
///
/// This design allows the parser to fully reflect the structure of the input.
///
/// # Errors
///
/// All failures are surfaced through a composed
/// [`ParserError<LexerError<I::Error, CalcError>, CalcError, CalcToken>`]:
/// - `I::Error` — errors from the input source,
/// - [`TermParserError`] — lexical/semantic errors (e.g., UTF-8, integer parsing,
///   symbol-table issues).
///
/// # Example
///
/// ```rust
/// # use arena_terms_parser::{TermToken, TermParser, TokenID, Value};
/// # use arena_terms::Arena;
/// # use try_next::{IterInput, TryNextWithContext};
/// let mut arena = Arena::new();
/// arena.define_default_opers().unwrap();
/// let input = IterInput::from("hello = 1 .\n foo =\n [5, 3, 2].\n (world, hello, 10).\n\n1000".bytes());
/// let mut parser = TermParser::try_new(input).unwrap();
/// let vs = parser.try_collect_with_context(&mut arena).unwrap();
/// assert_eq!(vs.len(), 4);
/// ```
///
/// [`Arena`]: arena_terms::Arena
/// [`Term`]: arena_terms::Term
/// [`OperDefs`]: crate::OperDefs
/// [`TermLexer`]: crate::TermLexer
/// [`TermToken`]: crate::TermToken
pub struct TermParser<I>
where
    I: TryNextWithContext<Arena, Item = u8, Error: std::fmt::Display + 'static>,
{
    pub(crate) parser: TermParser0<I>,
}

impl<I> TermParser<I>
where
    I: TryNextWithContext<Arena, Item = u8, Error: std::fmt::Display + 'static>,
{
    /// Creates a new [`TermParser`] for the given input stream and operator definitions.
    ///
    /// # Parameters
    /// - `input`: A fused iterator over bytes to be parsed.
    /// - `arena`: A term arena, used to initialized default operator defs.
    ///
    /// # Returns
    /// A fully initialized [`TermParser`] ready to parse Prolog-like terms.
    ///
    /// # Errors
    /// Returns an error if the lexer context cannot be initialized
    /// or if the generated parser tables fail to load.
    pub fn try_new(input: I) -> Result<Self, ParlexError> {
        let parser: TermParser0<I> = TermParser0::try_new(input)?;
        Ok(Self { parser })
    }

    /// Defines or extends operator definitions directly from a Prolog-like
    /// `op/6` term list read from a separate input source.
    ///
    /// This allows dynamic addition of new operator fixities and precedence
    /// rules during parsing.
    ///
    /// # Parameters
    /// - `arena`: Arena allocator used for constructing term structures.
    /// - `defs_input`: Input byte iterator yielding the operator definition terms.
    /// - `opers`: Optional initial operator table to extend.
    ///   If `None`, the default operator definitions are used.
    ///
    /// # Errors
    /// Returns an error if parsing the operator term list fails or produces
    /// an invalid operator specification.
    pub fn define_opers(arena: &mut Arena, defs_input: I) -> Result<(), ParlexError> {
        TermParser0::define_opers(arena, defs_input)
    }
}

impl<I> TryNextWithContext<Arena, (LexerStats, ParserStats)> for TermParser<I>
where
    I: TryNextWithContext<Arena, Item = u8, Error: std::fmt::Display + 'static>,
{
    /// Tokens produced by this lexer.
    type Item = Term;

    /// Unified error type.
    type Error = ParlexError;

    /// Advances the parser and returns the next token, or `None` at end of input.
    ///
    /// The provided `context` (an [`Arena`]) may be mutated by rule
    /// actions (for example, to intern terms). This method is fallible;
    /// both input and lexical errors are converted into [`Self::Error`].
    ///
    /// # End of Input
    ///
    /// When the lexer reaches the end of the input stream, it will typically
    /// emit a final [`TokenID::End`] token before returning `None`.
    ///
    /// This explicit *End* token is expected by the **Parlex parser** to
    /// signal successful termination of a complete parsing unit.
    /// Consumers should treat this token as a logical *end-of-sentence* or
    /// *end-of-expression* marker, depending on the grammar.
    ///
    /// If the input contains **multiple independent sentences or expressions**,
    /// the lexer may emit multiple `End` tokens—one after each completed unit.
    /// In such cases, the parser can restart or resume parsing after each `End`
    /// to produce multiple parse results from a single input stream.
    ///
    /// Once all input has been consumed, the lexer returns `None`.
    fn try_next_with_context(&mut self, context: &mut Arena) -> Result<Option<Term>, ParlexError> {
        while let Some(TermToken { value, .. }) = self.parser.try_next_with_context(context)? {
            match value {
                Value::Term(term) => return Ok(Some(term)),
                Value::None => continue,
                Value::Index(_) => {
                    return Err(ParlexError {
                        message: format!("index token not expected"),
                        span: None,
                    });
                }
            }
        }
        Ok(None)
    }

    fn stats(&self) -> (LexerStats, ParserStats) {
        self.parser.stats()
    }
}

/// Unit tests for the [`TermParser`] implementation.
#[cfg(test)]
mod tests {
    use super::*;
    use try_next::IterInput;

    const SAMPLE_DEFS: &str = r#"[
op(==(x,y),infix,350,none),
op(!=(x,y),infix,350,none),
op( <(x,y),infix,350,none),
op( >(x,y),infix,350,none),
op(<=(x,y),infix,350,none),
op(>=(x,y),infix,350,none),
op('+'(x,y),infix,380,left),
op('-'(x,y),infix,380,left),
op('-'(x),postfix,900,left, rename_to=some('postfix_minus')),
op('*'(x,y),infix,400,left),
op('/'(x,y),infix,400,left),
op('+'(x),prefix,800,right),
op(and(x,y),infix,300,left),
op(or(x,y),infix,250,left),
op(not(x),prefix,800,right),
]"#;

    fn parse(arena: &mut Arena, defs: Option<&str>, s: &str) -> Vec<Term> {
        let input = IterInput::from(s.bytes());
        let mut parser = TermParser::try_new(input).expect("cannot create parser");
        if let Some(defs) = defs {
            let defs_input = IterInput::from(defs.bytes());
            TermParser::define_opers(arena, defs_input).expect("cannot define ops");
        }
        let ts = parser
            .try_collect_with_context(arena)
            .expect("parser error");
        dbg!(parser.stats());
        ts
    }

    #[test]
    fn one_term() {
        let _ = env_logger::builder().is_test(true).try_init();
        let arena = &mut Arena::new();
        arena.define_default_opers().unwrap();
        let ts = parse(arena, Some(SAMPLE_DEFS), " . . 2 * 2 <= 5 . .");
        dbg!(&ts);
        let s = format!("{}", ts[0].display(arena));
        dbg!(&s);
        assert_eq!(ts.len(), 1);
        assert_eq!(s, "'<='('*'(2, 2), 5)");
    }

    #[test]
    #[should_panic]
    fn missing_ops() {
        let arena = &mut Arena::new();
        let _ts = parse(arena, None, "2 * 2 <= 5");
    }

    #[test]
    fn more_complicated_term() {
        let _ = env_logger::builder().is_test(true).try_init();
        let arena = &mut Arena::new();
        arena.define_default_opers().unwrap();
        let x = "(
[(1, 2) | unit] ++ foo(baz(1e-9)),
date{2025-09-30T18:24:22.154Z},
\"aaa{
1 + 2
}bbb{
3 * 4
}ccc\",
{player = {pos = {x = 0, y = 0}, health = 100}},
)";
        let ts = parse(arena, Some(SAMPLE_DEFS), x);
        let s = format!("{}", ts[0].display(arena));
        assert_eq!(ts.len(), 1);
        assert_eq!(
            s,
            "('++'([(1, 2) | unit], foo(baz(0.000000001))), date{2025-09-30T18:24:22.154+00:00}, '++'('++'('++'('++'(\"aaa\", '+'(1, 2)), \"bbb\"), '*'(3, 4)), \"ccc\"), \"player = {pos = {x = 0, y = 0}, health = 100}\")"
        );
    }
}
