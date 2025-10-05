//! Operator definitions and precedence handling.
//!
//! This module defines enums and utilities for representing and managing
//! operator fixity, associativity, and precedence in the arena terms parser.
//! Operators may appear in functional (`fun`), prefix, infix, or postfix
//! positions, and each is characterized by its [`Fixity`] and [`Assoc`].
//!
//! # Overview
//! Operators in Prolog-like syntax are context-sensitive and may serve multiple
//! syntactic roles depending on precedence and associativity. This module provides
//! data structures and functions for registering, validating, and querying
//! operator definitions used during parsing.
//!
//! # Components
//! - [`Fixity`]: Enumerates operator positions (`Fun`, `Prefix`, `Infix`, `Postfix`).
//! - [`Assoc`]: Describes associativity (`Left`, `Right`, `NonAssoc`).
//! - [`OperDefs`]: Stores and manages operator definitions, providing fast lookup
//!   by name and fixity.
//!
//! # Usage
//! Operator definitions are typically registered at parser initialization,
//! enabling grammar-aware expression parsing and disambiguation.
//!
//! # See Also
//! - [`crate::parser`]: Consumes operator definitions during expression parsing.
//! - [`arena_terms`]: Provides the underlying term representation used in operators.

use anyhow::{Context, Result, anyhow, bail};
use arena_terms::{Arena, Term, View};
use indexmap::IndexMap;
use smartstring::alias::String;
use std::collections::HashSet;
use std::fmt;
use std::str::FromStr;

/// Defines the syntactic position (fixity) of an operator.
///
/// Operators in Prolog-like syntax can appear in different structural positions
/// depending on their form. The `Fixity` enum captures these roles and is used
/// to categorize operators within the parser and operator definition tables.
///
/// # Variants
/// - [`Fun`]: A functional (non-operator) form, e.g., `f(x, y)`.
/// - [`Prefix`]: A prefix operator appearing before its operand, e.g., `-x`.
/// - [`Infix`]: An infix operator appearing between two operands, e.g., `x + y`.
/// - [`Postfix`]: A postfix operator appearing after its operand, e.g., `x!`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Fixity {
    /// Functional (non-operator) position, e.g. `f(x)`.
    Fun = 0,

    /// Prefix operator, appearing before its operand, e.g. `-x`.
    Prefix = 1,

    /// Infix operator, appearing between operands, e.g. `x + y`.
    Infix = 2,

    /// Postfix operator, appearing after its operand, e.g., `x!`.
    Postfix = 3,
}

impl Fixity {
    /// The total number of fixity variants.
    pub const COUNT: usize = 4;

    /// String representations of each fixity variant, in declaration order.
    pub const STRS: &[&str] = &["fun", "prefix", "infix", "postfix"];
}

impl From<Fixity> for String {
    /// Converts a [`Fixity`] into its lowercase string representation.
    fn from(f: Fixity) -> Self {
        Fixity::STRS[Into::<usize>::into(f)].into()
    }
}

impl From<Fixity> for usize {
    /// Converts a [`Fixity`] value into its numeric index (0–3).
    fn from(f: Fixity) -> Self {
        f as usize
    }
}

impl fmt::Display for Fixity {
    /// Formats the fixity as its canonical lowercase name.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(String::from(*self).as_str())
    }
}

impl TryFrom<&str> for Fixity {
    type Error = ParseFixityError;
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        s.parse()
    }
}

impl TryFrom<String> for Fixity {
    type Error = ParseFixityError;
    fn try_from(s: String) -> Result<Self, Self::Error> {
        s.as_str().parse()
    }
}

/// Error type returned when parsing a [`Fixity`] from a string fails.
///
/// This error indicates that the provided input string does not correspond
/// to any known fixity variant (`"fun"`, `"prefix"`, `"infix"`, or `"postfix"`).
#[derive(Debug, Clone)]
pub struct ParseFixityError(String);

impl fmt::Display for ParseFixityError {
    /// Formats the error message indicating the invalid fixity string.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "invalid fixity: {}", self.0)
    }
}
impl std::error::Error for ParseFixityError {}

/// Parses a string into a [`Fixity`] variant.
///
/// Accepts canonical lowercase names: `"fun"`, `"prefix"`, `"infix"`, or `"postfix"`.
/// Returns a [`ParseFixityError`] if the input string does not match any known fixity.
impl FromStr for Fixity {
    type Err = ParseFixityError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "fun" => Ok(Fixity::Fun),
            "prefix" => Ok(Fixity::Prefix),
            "infix" => Ok(Fixity::Infix),
            "postfix" => Ok(Fixity::Postfix),
            other => Err(ParseFixityError(String::from(other))),
        }
    }
}

/// Operator associativity classification.
///
/// [`Assoc`] determines how operators of the same precedence are grouped during parsing.
/// It supports left-, right-, and non-associative operators.
///
/// | Variant | Description |
/// |----------|--------------|
/// | [`Assoc::None`]  | Non-associative — cannot chain with itself. |
/// | [`Assoc::Left`]  | Left-associative — groups from left to right. |
/// | [`Assoc::Right`] | Right-associative — groups from right to left. |
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Assoc {
    /// Non-associative operator.
    None = 0,
    /// Left-associative operator.
    Left = 1,
    /// Right-associative operator.
    Right = 2,
}

impl Assoc {
    /// Total number of associativity variants.
    pub const COUNT: usize = 3;

    /// Canonical string representations for each variant.
    pub const STRS: &[&str] = &["none", "left", "right"];
}

impl From<Assoc> for String {
    /// Converts an [`Assoc`] variant into its canonical lowercase string.
    fn from(a: Assoc) -> Self {
        Assoc::STRS[Into::<usize>::into(a)].into()
    }
}

impl From<Assoc> for usize {
    /// Converts an [`Assoc`] variant into its numeric discriminant.
    fn from(a: Assoc) -> Self {
        a as usize
    }
}

impl fmt::Display for Assoc {
    /// Formats the associativity as its canonical lowercase name.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(String::from(*self).as_str())
    }
}

/// Error type returned when parsing an [`Assoc`] from a string fails.
///
/// This error indicates that the provided input string does not correspond
/// to any known associativity variant (`"none"`, `"left"`, or `"right"`).
#[derive(Debug, Clone)]
pub struct ParseAssocError(String);

impl fmt::Display for ParseAssocError {
    /// Formats the error message indicating the invalid associativity string.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "invalid associativity: {}", self.0)
    }
}

impl std::error::Error for ParseAssocError {}

impl FromStr for Assoc {
    type Err = ParseAssocError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "none" => Ok(Assoc::None),
            "left" => Ok(Assoc::Left),
            "right" => Ok(Assoc::Right),
            other => Err(ParseAssocError(String::from(other))),
        }
    }
}

impl TryFrom<&str> for Assoc {
    type Error = ParseAssocError;
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        s.parse()
    }
}

impl TryFrom<String> for Assoc {
    type Error = ParseAssocError;
    fn try_from(s: String) -> Result<Self, Self::Error> {
        s.as_str().parse()
    }
}

/// Represents an additional argument associated with an operator definition.
///
/// Each [`OperArg`] defines a named parameter (an atom) and an optional
/// default value stored as an [`arena_terms::Term`].
#[derive(Debug, Clone)]
pub struct OperArg {
    /// The argument name (atom identifier).
    pub name: String,
    /// Optional default value for the argument.
    pub default: Option<Term>,
}

/// Default precedence values used for operator definitions.
///
/// - [`NON_OPER_PREC`] — precedence value for non-operators (0).
/// - [`MIN_OPER_PREC`] — minimum allowed precedence (0).
/// - [`MAX_OPER_PREC`] — maximum allowed precedence (1200).
pub const NON_OPER_PREC: usize = 0;
pub const MIN_OPER_PREC: usize = 0;
pub const MAX_OPER_PREC: usize = 1200;

/// Defines a single operator, including its fixity, precedence, associativity,
/// and optional additional parameters.
///
/// Each operator definition describes how the parser should treat a symbol
/// syntactically, including its argument behavior and binding strength.
///
/// # Field Rules
/// - `prec` must be `0` for [`Fixity::Fun`].
/// - `assoc` must be:
///   - [`Assoc::None`] for [`Fixity::Fun`],
///   - [`Assoc::Right`] for [`Fixity::Prefix`],
///   - [`Assoc::Left`] for [`Fixity::Postfix`].
#[derive(Debug, Clone)]
pub struct OperDef {
    /// Operator fixity (function, prefix, infix, or postfix).
    pub fixity: Fixity,
    /// Operator precedence (`0`–`1200`).
    ///
    /// Higher numbers indicate **tighter binding**.
    /// Must be `0` for [`Fixity::Fun`].
    pub prec: usize,
    /// Operator associativity (depends on fixity).
    pub assoc: Assoc,
    /// Optional extra arguments beyond the operator’s required operands.
    pub args: Vec<OperArg>,
    /// Optional renaming target (atom term).
    pub rename_to: Option<Term>,
    /// Whether this operator’s fixity should be embedded in generated term.
    pub embed_fixity: bool,
}

/// Container for operator definitions indexed by [`Fixity`].
///
/// Each entry in the internal array corresponds to one fixity variant
/// (function, prefix, infix, or postfix).
#[derive(Debug, Clone)]
pub struct OperDefTab {
    tab: [Option<OperDef>; Fixity::COUNT],
}

/// Central registry of all operator definitions.
///
/// [`OperDefs`] maps operator names to a table of definitions by fixity.
/// Provides fast lookup of operator behavior and metadata.
#[derive(Debug, Clone, Default)]
pub struct OperDefs {
    map: IndexMap<String, OperDefTab>,
}

/// Shared empty operator definition table constant.
static EMPTY_OPER_DEF_TAB: OperDefTab = OperDefTab::new();

impl OperDef {
    /// Returns the number of required operands for a given [`Fixity`].
    ///
    /// - [`Fixity::Fun`] → `0`
    /// - [`Fixity::Prefix`] → `1`
    /// - [`Fixity::Infix`] → `2`
    /// - [`Fixity::Postfix`] → `1`
    pub fn required_arity(fixity: Fixity) -> usize {
        match fixity {
            Fixity::Fun => 0,
            Fixity::Prefix => 1,
            Fixity::Infix => 2,
            Fixity::Postfix => 1,
        }
    }
}

impl OperDefTab {
    /// Creates a new, empty [`OperDefTab`] with all fixity slots unset.
    ///
    /// Each entry in the table corresponds to a [`Fixity`] variant
    /// (`fun`, `prefix`, `infix`, or `postfix`), all initialized to `None`.
    pub const fn new() -> Self {
        Self {
            tab: [const { None }; Fixity::COUNT],
        }
    }

    /// Returns `true` if this table defines a function (`fun`) operator.
    pub fn is_fun(&self) -> bool {
        self.tab[0].is_some()
    }

    /// Returns `true` if this table defines at least one operator fixity.
    pub fn is_oper(&self) -> bool {
        self.tab[1..].iter().any(|x| x.is_some())
    }

    /// Retrieves the operator definition for the given [`Fixity`], if present.
    pub fn get_op_def(&self, fixity: Fixity) -> Option<&OperDef> {
        self.tab[usize::from(fixity)].as_ref()
    }
}

impl std::ops::Index<Fixity> for OperDefTab {
    type Output = Option<OperDef>;

    /// Indexes the table by [`Fixity`], returning the corresponding definition.
    ///
    /// # Panics
    /// Panics if the fixity discriminant is out of range (should never occur).
    fn index(&self, i: Fixity) -> &Self::Output {
        let i: usize = i.into();
        &self.tab[i]
    }
}

impl std::ops::IndexMut<Fixity> for OperDefTab {
    /// Mutable indexing by [`Fixity`], allowing modification of the definition.
    ///
    /// # Panics
    /// Panics if the fixity discriminant is out of range (should never occur).
    fn index_mut(&mut self, i: Fixity) -> &mut Self::Output {
        let i: usize = i.into();
        &mut self.tab[i]
    }
}

impl OperDefs {
    /// Creates an empty [`OperDefs`] registry.
    ///
    /// Initializes an operator definition map with no entries.
    pub fn new() -> Self {
        Self {
            map: IndexMap::new(),
        }
    }

    /// Builds an [`OperDefs`] table from a parsed term representation.
    ///
    /// This helper reads operator specifications encoded as [`arena_terms::Term`] values
    /// and populates the operator definition registry accordingly.
    ///
    /// # Parameters
    /// - `arena`: The [`Arena`] used to allocate or access term data.
    /// - `ops`: The root [`Term`] containing operator definitions.
    ///
    /// # Errors
    /// Returns an error if operator parsing or validation fails.
    pub fn try_from_ops(arena: &Arena, ops: Term) -> Result<Self> {
        let mut oper_defs = Self::new();
        oper_defs.define_opers(arena, ops)?;
        Ok(oper_defs)
    }

    /// Returns the total number of operator entries in this registry.
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Looks up an operator by name and returns its index, if defined.
    ///
    /// # Parameters
    /// - `name`: The operator name to query.
    ///
    /// # Returns
    /// The operator’s internal index if found, or `None` if not present.
    pub fn lookup(&self, name: &str) -> Option<usize> {
        self.map.get_index_of(name)
    }

    /// Retrieves an operator definition table by index.
    ///
    /// Returns a reference to the corresponding [`OperDefTab`],
    /// or [`EMPTY_OPER_DEF_TAB`] if the index is `None` or out of bounds.
    pub fn get(&self, index: Option<usize>) -> &OperDefTab {
        match index {
            Some(index) => match self.map.get_index(index) {
                Some((_, tab)) => tab,
                None => &EMPTY_OPER_DEF_TAB,
            },
            None => &EMPTY_OPER_DEF_TAB,
        }
    }

    /// Defines a single operator entry from a parsed [`arena_terms::Term`] structure.
    ///
    /// This function ingests a Prolog-style operator definition term of the form:
    ///
    /// ```prolog
    /// op(
    ///     oper: atom | func(arg: atom | '='(name: atom, default: term)), ...,
    ///     type: 'fun' | 'prefix' | 'infix' | 'postfix',
    ///     prec: 0..1200,          % must be 0 for fixity = 'fun'
    ///     assoc: 'none' | 'left' | 'right',
    ///     rename_to: 'none' | some(new_name: atom),
    ///     embed_type: 'false' | 'true'
    /// ).
    /// ```
    ///
    /// Each `op/1` term specifies one operator, including its name, fixity, precedence,
    /// associativity, optional renaming target, and embedding behavior.
    ///
    /// # Parameters
    /// - `arena`: The [`Arena`] providing term access and allocation.
    /// - `op`: The [`Term`] describing the operator declaration.
    ///
    /// # Returns
    /// - `Ok(())` if the operator was successfully parsed and registered.
    ///
    /// # Errors
    /// Returns an error if the operator definition is invalid, malformed, or violates
    /// fixity/precedence/associativity constraints.
    pub fn define_oper(&mut self, arena: &Arena, op: Term) -> Result<()> {
        const BOOLS: &[&str] = &["false", "true"];

        let (_, [oper, fixity, prec, assoc, rename_to, embed_fixity]) =
            op.unpack_func(arena, &["op"])?;

        let (functor, args) = oper.unpack_func_any(arena, &[])?;
        let name = functor.atom_name(arena)?;

        let fixity = Fixity::try_from(fixity.unpack_atom(arena, Fixity::STRS)?)?;
        let prec = prec.unpack_int(arena)?.try_into()?;
        let assoc = Assoc::try_from(assoc.unpack_atom(arena, Assoc::STRS)?)?;
        let embed_fixity = embed_fixity.unpack_atom(arena, BOOLS)? == "true";

        let args = args
            .into_iter()
            .map(|arg| {
                Ok(match arg.view(arena)? {
                    View::Atom(name) => OperArg {
                        name: String::from(name),
                        default: None,
                    },
                    View::Func(ar, _, _) => {
                        let (_, [name, term]) = arg.unpack_func(ar, &["="])?;
                        OperArg {
                            name: String::from(name.atom_name(ar)?),
                            default: Some(term),
                        }
                    }
                    _ => bail!("oper arg must be an atom or =(atom, term) in {:?}", name),
                })
            })
            .collect::<Result<Vec<_>>>()?;

        let required_arity = OperDef::required_arity(fixity);
        if args.len() < required_arity {
            bail!(
                "operator {:?} requires at least {} argument(s)",
                name,
                required_arity
            );
        }

        if args[..required_arity].iter().any(|x| x.default.is_some()) {
            bail!("defaults are not allowed for required operator arguments");
        }

        let unique_arg_names: HashSet<_> = args.iter().map(|x| &x.name).cloned().collect();
        if unique_arg_names.len() != args.len() {
            bail!("duplicate arguments in {:?}", name);
        }

        let rename_to = match rename_to.view(arena)? {
            View::Atom("none") => None,
            View::Func(ar, _, _) => {
                let (_, [rename_to]) = rename_to.unpack_func(ar, &["some"])?;
                Some(rename_to)
            }
            _ => bail!("rename_to must be 'none' | some(atom)"),
        };

        if matches!(fixity, Fixity::Fun) && prec != NON_OPER_PREC {
            bail!("{:?} must be assigned precedence 0", name);
        }
        if !matches!(fixity, Fixity::Fun) && (prec < MIN_OPER_PREC || prec > MAX_OPER_PREC) {
            bail!(
                "precedence {} is out of range for operator {:?} with type {:?} (expected {}–{})",
                prec,
                name,
                fixity,
                MIN_OPER_PREC,
                MAX_OPER_PREC,
            );
        }
        if matches!((fixity, assoc), (Fixity::Prefix, Assoc::Left))
            || matches!((fixity, assoc), (Fixity::Postfix, Assoc::Right))
        {
            bail!(
                "operator {:?} with type {:?} cannot have associativity {:?}",
                name,
                fixity,
                assoc
            );
        }

        // This check is intentionally disabled to preserve compatibility
        // with the behavior of the original C implementation
        #[cfg(false)]
        if matches!((fixity, assoc), (Fixity::Fun, Assoc::Left | Assoc::Right)) {
            bail!(
                "{:?} with type {:?} cannot have associativity {:?}",
                name,
                fixity,
                assoc
            );
        }

        let tab = self
            .map
            .entry(String::from(name))
            .or_insert_with(OperDefTab::new);

        if matches!(fixity, Fixity::Fun) && tab.is_oper() {
            bail!(
                "cannot define {:?} with type {:?}; it is already defined as an operator with a different type",
                name,
                fixity,
            );
        }

        if matches!(fixity, Fixity::Prefix | Fixity::Infix | Fixity::Postfix)
            && tab.tab[Into::<usize>::into(Fixity::Fun)].is_some()
        {
            bail!(
                "cannot define {:?} as an operator with type {:?}; it is already defined with type Fun",
                name,
                fixity,
            );
        }

        if tab[fixity].is_some() {
            bail!("cannot re-define {:?}", name);
        }

        tab[fixity] = Some(OperDef {
            fixity,
            prec,
            assoc,
            rename_to,
            embed_fixity,
            args,
        });

        Ok(())
    }

    /// Defines one or more operators from a parsed [`arena_terms::Term`] structure.
    ///
    /// This method accepts either:
    /// - A list of operator terms (each of which is passed to [`define_oper`]), or
    /// - A single operator term (`op(...)`) to be defined directly.
    ///
    /// Each term is ingested and registered according to its fixity, precedence,
    /// associativity, and optional metadata.
    ///
    /// # Parameters
    /// - `arena`: The [`Arena`] providing term access and allocation.
    /// - `term`: Either a list of operator definitions or a single operator term.
    ///
    /// # Returns
    /// - `Ok(())` if all operator definitions were successfully processed.
    ///
    /// # Errors
    /// Returns an error if any individual operator definition is invalid,
    /// malformed, or violates fixity/precedence/associativity constraints.
    pub fn define_opers(&mut self, arena: &Arena, term: Term) -> Result<()> {
        match term.view(arena)? {
            View::List(arena, ts, _) => {
                for t in ts {
                    self.define_oper(arena, *t)?;
                }
            }
            _ => {
                self.define_oper(arena, term)?;
            }
        }
        Ok(())
    }
}
