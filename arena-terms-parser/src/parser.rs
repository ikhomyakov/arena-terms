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

use crate::{
    Assoc, Fixity, MAX_OPER_PREC, MIN_OPER_PREC, OperDef, OperDefs, TermLexer, TermLexerDriver,
    TermParserError, TermToken, TokenID, Value, bail,
};
use arena_terms::{Arena, IntoTerm, Term, View, atom, func, list};
use parlex::{
    LexerDriver, LexerError, Parser, ParserAction, ParserData, ParserDriver, ParserError,
};
use parser_data::{AmbigID, ParData, ProdID, StateID};
use smartstring::alias::String;
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
    I: TryNextWithContext<Arena, Item = TermToken>,
{
    /// Parser metadata generated from the calculator grammar.
    type ParserData = ParData;

    /// Token type consumed by the parser.
    type Token = TermToken;

    /// Concrete parser engine type.
    type Parser = Parser<I, Self, Self::Context>;

    /// Error type for semantic or parsing failures.
    type Error = TermParserError;

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
        _arena: &mut Self::Context,
        ambig: <Self::ParserData as ParserData>::AmbigID,
        tok2: &Self::Token,
    ) -> Result<ParserAction<StateID, ProdID, AmbigID>, Self::Error> {
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
            _ => bail!(
                "unexpected conflict: reduction of {:?} with shifting token {:?}",
                prod_id,
                tok2
            ),
        };

        let op_tab1 = parser.lexer..lexer.opers.get(tok1.op_tab_index);
        let op_tab2 = parser.lexer.opers.get(tok2.op_tab_index);

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
                    bail!(
                        "precedence conflict: cannot chain non-associative operator {:?}; use parenthesis",
                        tok1
                    );
                }
                if op_tab2[Fixity::Infix]
                    .as_ref()
                    .is_some_and(|x| x.assoc == Assoc::None)
                    || op_tab2[Fixity::Postfix]
                        .as_ref()
                        .is_some_and(|x| x.assoc == Assoc::None)
                {
                    bail!(
                        "precedence conflict: cannot chain non-associative operator {:?}; use parenthesis",
                        tok2
                    );
                }
                if op_tab2[Fixity::Infix]
                    .as_ref()
                    .is_some_and(|x| x.assoc != assoc1)
                    || op_tab2[Fixity::Postfix]
                        .as_ref()
                        .is_some_and(|x| x.assoc != assoc1)
                {
                    bail!(
                        "associativity conflict: cannot chain operators {:?} and {:?}; use parenthesis",
                        tok1,
                        tok2
                    );
                } else {
                    if assoc1 == Assoc::Left {
                        Ok(reduce_action)
                    } else {
                        Ok(shift_action)
                    }
                }
            } else {
                bail!(
                    "precedence conflict: cannot chain operators {:?} and {:?}; use parenthesis",
                    tok1,
                    tok2
                );
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
    ) -> Result<(), Self::Error> {
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
                parser.tokens_push(TermToken::new(TokenID::Term, Value::None, token.line_no));
            }

            ProdID::Term4 => {
                // Term -> .
                parser.tokens_pop();
                parser.tokens_push(TermToken::new(TokenID::Term, Value::None, token.line_no));
            }

            ProdID::Func => {
                // Expr -> func Seq )
                parser.tokens_pop();
                let index = usize::try_from(parser.tokens_pop().value)?;
                let func_tok = parser.tokens_pop();
                let line_no = func_tok.line_no;
                let op_tab_index = func_tok.op_tab_index;
                let functor = Term::try_from(func_tok.value)?;

                let vs = std::iter::once(&functor).chain(self.terms[index..].iter());
                let term = arena.funcv(vs)?;
                self.terms.truncate(index);

                let term = self.normalize_term(arena, term, Fixity::Fun, op_tab_index)?;

                parser.tokens_push(TermToken::new(TokenID::Expr, Value::Term(term), line_no));
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
                    left_brack_tok.line_no,
                ));
            }

            ProdID::Nil => {
                // Expr -> [ ]
                parser.tokens_pop();
                let left_brack_tok = parser.tokens_pop();
                parser.tokens_push(TermToken::new(
                    TokenID::Expr,
                    Value::Term(Term::NIL),
                    left_brack_tok.line_no,
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
                    left_brack_tok.line_no,
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
                    left_paren_tok.line_no,
                ));
            }

            ProdID::Unit => {
                // Expr -> ( )
                parser.tokens_pop();
                let left_paren_tok = parser.tokens_pop();
                parser.tokens_push(TermToken::new(
                    TokenID::Expr,
                    Value::Term(Term::UNIT),
                    left_paren_tok.line_no,
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
                let line_no = atom_tok.line_no;
                let op_tab_index = atom_tok.op_tab_index;

                let atom = Term::try_from(atom_tok.value)?;

                let term = self.normalize_term(arena, atom, Fixity::Fun, op_tab_index)?;

                parser.tokens_push(TermToken::new(TokenID::Expr, Value::Term(term), line_no));
            }

            ProdID::Infix1 => {
                // Expr -> Expr atomOper Expr
                let expr2_tok = parser.tokens_pop();
                let oper_tok = parser.tokens_pop();
                let expr1_tok = parser.tokens_pop();
                let line_no = expr1_tok.line_no;
                let op_tab_index = oper_tok.op_tab_index;

                let expr2 = Term::try_from(expr2_tok.value)?;
                let oper = Term::try_from(oper_tok.value)?;
                let expr1 = Term::try_from(expr1_tok.value)?;

                let term = arena.funcv([oper, expr1, expr2])?;
                let term = self.normalize_term(arena, term, Fixity::Infix, op_tab_index)?;

                parser.tokens_push(TermToken::new(TokenID::Expr, Value::Term(term), line_no));
            }

            ProdID::Infix2 => {
                // Expr -> Expr func Seq ) Expr
                let expr2_tok = parser.tokens_pop();
                parser.tokens_pop();
                let index = usize::try_from(parser.tokens_pop().value)?;
                let oper_tok = parser.tokens_pop();
                let expr1_tok = parser.tokens_pop();
                let line_no = expr1_tok.line_no;
                let op_tab_index = oper_tok.op_tab_index;

                let expr2 = Term::try_from(expr2_tok.value)?;
                let oper = Term::try_from(oper_tok.value)?;
                let expr1 = Term::try_from(expr1_tok.value)?;

                let xs = [oper, expr1, expr2];
                let vs = xs.iter().chain(self.terms[index..].iter());
                let term = arena.funcv(vs)?;
                self.terms.truncate(index);

                let term = self.normalize_term(arena, term, Fixity::Infix, op_tab_index)?;

                parser.tokens_push(TermToken::new(TokenID::Expr, Value::Term(term), line_no));
            }

            ProdID::Prefix1 => {
                // Expr -> atom Expr
                let expr1_tok = parser.tokens_pop();
                let oper_tok = parser.tokens_pop();
                let line_no = oper_tok.line_no;
                let op_tab_index = oper_tok.op_tab_index;

                let expr1 = Term::try_from(expr1_tok.value)?;
                let oper = Term::try_from(oper_tok.value)?;

                let term = match oper.view(arena)? {
                    // Arena terms parser currently gives special treatment to unary minus
                    // on integer and real literals (it directly negates them).
                    // TODO: Consider handling minus at the lexical level.
                    View::Atom(s)
                        if s == "-"
                            && matches!(expr1.view(arena)?, View::Int(_) | View::Real(_)) =>
                    {
                        match expr1.view(arena)? {
                            View::Int(i) => arena.int(-i),
                            View::Real(r) => arena.real(-r),
                            _ => unreachable!(),
                        }
                    }
                    _ => {
                        let term = arena.funcv([oper, expr1])?;
                        self.normalize_term(arena, term, Fixity::Prefix, op_tab_index)?
                    }
                };

                parser.tokens_push(TermToken::new(TokenID::Expr, Value::Term(term), line_no));
            }

            ProdID::Prefix2 => {
                // Expr -> func Seq ) Expr
                let expr1_tok = parser.tokens_pop();
                parser.tokens_pop();
                let index = usize::try_from(parser.tokens_pop().value)?;
                let oper_tok = parser.tokens_pop();
                let line_no = oper_tok.line_no;
                let op_tab_index = oper_tok.op_tab_index;

                let oper = Term::try_from(oper_tok.value)?;
                let expr1 = Term::try_from(expr1_tok.value)?;

                let xs = [oper, expr1];
                let vs = xs.iter().chain(self.terms[index..].iter());
                let term = arena.funcv(vs)?;
                self.terms.truncate(index);

                let term = self.normalize_term(arena, term, Fixity::Prefix, op_tab_index)?;

                parser.tokens_push(TermToken::new(TokenID::Expr, Value::Term(term), line_no));
            }

            ProdID::Postfix1 => {
                // Expr -> Expr atomOper
                let oper_tok = parser.tokens_pop();
                let expr1_tok = parser.tokens_pop();
                let line_no = expr1_tok.line_no;
                let op_tab_index = oper_tok.op_tab_index;

                let oper = Term::try_from(oper_tok.value)?;
                let expr1 = Term::try_from(expr1_tok.value)?;

                let term = arena.funcv([oper, expr1])?;
                let term = self.normalize_term(arena, term, Fixity::Postfix, op_tab_index)?;

                parser.tokens_push(TermToken::new(TokenID::Expr, Value::Term(term), line_no));
            }

            ProdID::Postfix2 => {
                // Expr -> Expr func Seq )
                parser.tokens_pop();
                let index = usize::try_from(parser.tokens_pop().value)?;
                let oper_tok = parser.tokens_pop();
                let expr1_tok = parser.tokens_pop();
                let line_no = expr1_tok.line_no;
                let op_tab_index = oper_tok.op_tab_index;

                let oper = Term::try_from(oper_tok.value)?;
                let expr1 = Term::try_from(expr1_tok.value)?;

                let xs = [oper, expr1];
                let vs = xs.iter().chain(self.terms[index..].iter());
                let term = arena.funcv(vs)?;
                self.terms.truncate(index);

                let term = self.normalize_term(arena, term, Fixity::Postfix, op_tab_index)?;

                parser.tokens_push(TermToken::new(TokenID::Expr, Value::Term(term), line_no));
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
                let line_no = expr_tok.line_no;
                let expr = Term::try_from(expr_tok.value)?;

                let index = self.terms.len();
                self.terms.push(expr);

                parser.tokens_push(TermToken::new(
                    TokenID::BareSeq,
                    Value::Index(index),
                    line_no,
                ));
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
/// The [`TermParser`] drives the parsing of Prolog-style terms using the
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
///   [`TryNextWithContext<Arena, Item = u8>`].
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
/// # use parlex_calc::{TermToken, TermParser, TokenID, Value};
/// # use arena_terms::Arena;
/// # use try_next::{IterInput, TryNextWithContext};
/// let mut arena = Arena::new();
/// let input = IterInput::from("hello = 1 .\n foo =\n [5, 3, 2].\n (world, hello, 10).\n\n1000".bytes());
/// let mut parser = TermParser::try_new(input, None).unwrap();
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
    I: TryNextWithContext<Arena, Item = u8>,
{
    pub(crate) parser: Parser<TermLexer<I>, TermParserDriver<TermLexer<I>>, Arena>,
}

impl<I> TermParser<I>
where
    I: TryNextWithContext<Arena, Item = u8>,
{
    /// Creates a new [`TermParser`] for the given input stream and operator definitions.
    ///
    /// # Parameters
    /// - `input`: A fused iterator over bytes to be parsed.
    /// - `arena`: A term arena, used to initialized default operator defs.
    /// - `opers`: Optional [`OperDefs`] defining operator precedence and fixity.
    ///   If `None`, the default operator definitions are used.
    ///
    /// # Returns
    /// A fully initialized [`TermParser`] ready to parse Prolog-like terms.
    ///
    /// # Errors
    /// Returns an error if the lexer context cannot be initialized
    /// or if the generated parser tables fail to load.
    pub fn try_new(
        input: I,
        arena: &mut Arena,
        opers: Option<OperDefs>,
    ) -> Result<
        Self,
        ParserError<
            LexerError<
                <I as TryNextWithContext<Arena>>::Error,
                <TermLexerDriver<I> as LexerDriver>::Error,
            >,
            <TermParserDriver<TermLexer<I>> as ParserDriver>::Error,
            TermToken,
        >,
    > {
        let opers = match opers {
            Some(opers) => opers,
            None => parser_oper_defs(arena),
        };

        let lexer = TermLexer::try_new(input, Some(opers)).map_err(ParserError::Lexer)?;
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
    pub fn define_opers<J: TryNextWithContext<Arena, Item = u8>>(
        &mut self,
        arena: &mut Arena,
        defs_input: J,
    ) -> Result<(), TermParserError> {
        let lexer_driver = self
            .parser
            .lexer
            .lexer
            .driver
            .take()
            .ok_or_else(|| LexerError::MissingDriver)?;
        let mut defs_parser = TermParser::try_new(defs_input, arena, Some(lexer_driver.opers))?;
        while let Some(term) = defs_parser.try_next_term(arena)? {
            log::trace!("Stats: {:?}", defs_parser.stats(),);
            defs_parser.opers_mut().define_opers(arena, term)?;
        }
        let defs_opers = std::mem::take(&mut defs_parser.opers_mut());
        *self.opers_mut() = defs_opers;

        self.parser.lexer.lexer.driver = Some(lexer_driver);
        Ok(())
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
        let mut parser = TermParser::try_new(input, arena, None).expect("cannot create parser");
        if let Some(defs) = defs {
            let defs_input = IterInput::from(defs.bytes());
            parser
                .define_opers(arena, defs_input)
                .expect("cannot define ops");
        }
        parser.try_collect_terms(arena).expect("parser error")
    }

    #[test]
    fn one_term() {
        let _ = env_logger::builder().is_test(true).try_init();
        let arena = &mut Arena::new();
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
