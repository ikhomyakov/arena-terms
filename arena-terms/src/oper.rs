//! Operator definitions, precedence, and compound term argument metadata.
//!
//! This module defines types and utilities for representing and managing
//! operator fixity, associativity, precedence, and compound term argument
//! specifications. Operators may appear in prefix, infix, or postfix positions,
//! each characterized by its [`Fixity`] and [`Assoc`]. Non-operator compound terms
//! are represented using the `fun` fixity for uniform handling within
//! the same framework.
//!
//! These definitions may also include **named arguments** and **default
//! values**, which describe the structure of compound terms. Using this
//! metadata, the [`Arena`] can "normalize" partially defined compounds by
//! filling in defaults and automatically reordering arguments according to
//! their declared names. The arena also exposes this information to the
//! `arena-terms-parser`, allowing the parser to interpret and construct
//! terms consistently with defined operators.

use crate::{Arena, IntoTerm, Term, TermError, View, atom, func, list};
use indexmap::IndexMap;
use smartstring::alias::String;
use std::collections::HashSet;
use std::fmt;
use std::str::FromStr;

/// Returns `TermError::OperDef` with a formatted message.
///
/// # Example
/// ```rust, ignore
/// bail!("invalid value: {}", val);
/// ```
macro_rules! bail {
    ($($arg:tt)*) => {
        return Err(crate::TermError::OperDef(String::from(format!($($arg)*))))
    }
}

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
    type Error = TermError;
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        s.parse()
    }
}

impl TryFrom<String> for Fixity {
    type Error = TermError;
    fn try_from(s: String) -> Result<Self, Self::Error> {
        s.as_str().parse()
    }
}

/// Parses a string into a [`Fixity`] variant.
///
/// Accepts canonical lowercase names: `"fun"`, `"prefix"`, `"infix"`, or `"postfix"`.
/// Returns a [`ParseFixityError`] if the input string does not match any known fixity.
impl FromStr for Fixity {
    type Err = TermError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "fun" => Ok(Fixity::Fun),
            "prefix" => Ok(Fixity::Prefix),
            "infix" => Ok(Fixity::Infix),
            "postfix" => Ok(Fixity::Postfix),
            other => Err(TermError::InvalidFixity(String::from(other))),
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

impl FromStr for Assoc {
    type Err = TermError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "none" => Ok(Assoc::None),
            "left" => Ok(Assoc::Left),
            "right" => Ok(Assoc::Right),
            other => Err(TermError::InvalidAssoc(String::from(other))),
        }
    }
}

impl TryFrom<&str> for Assoc {
    type Error = TermError;
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        s.parse()
    }
}

impl TryFrom<String> for Assoc {
    type Error = TermError;
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
pub const NON_OPER_PREC: i64 = 0;
pub const MIN_OPER_PREC: i64 = 0;
pub const MAX_OPER_PREC: i64 = 1200;

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
    pub prec: i64,
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
}

impl Arena {
    /// Looks up an operator by name and returns its index, if defined.
    ///
    /// # Parameters
    /// - `name`: The operator name to query.
    ///
    /// # Returns
    /// The operator’s internal index if found, or `None` if not present.
    pub fn lookup_oper(&self, name: &str) -> Option<usize> {
        self.opers.map.get_index_of(name)
    }

    /// Retrieves an operator definition table by index.
    ///
    /// Returns a reference to the corresponding [`OperDefTab`],
    /// or [`EMPTY_OPER_DEF_TAB`] if the index is `None` or out of bounds.
    pub fn get_oper(&self, index: Option<usize>) -> &OperDefTab {
        match index {
            Some(index) => match self.opers.map.get_index(index) {
                Some((_, tab)) => tab,
                None => &EMPTY_OPER_DEF_TAB,
            },
            None => &EMPTY_OPER_DEF_TAB,
        }
    }

    /// Returns the total number of operator entries in this registry.
    pub fn opers_len(&self) -> usize {
        self.opers.map.len()
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
    pub fn define_oper(&mut self, op: Term) -> Result<(), TermError> {
        const BOOLS: &[&str] = &["false", "true"];

        let (_, [oper, fixity, prec, assoc, rename_to, embed_fixity]) =
            op.unpack_func(self, &["op"])?;

        let (functor, args) = oper.unpack_func_any(self, &[])?;
        let name = String::from(functor.atom_name(self)?);

        let fixity = Fixity::try_from(fixity.unpack_atom(self, Fixity::STRS)?)?;

        let prec = prec.unpack_int(self)?;

        if prec < MIN_OPER_PREC || prec > MAX_OPER_PREC {
            bail!(
                "precedence {} out of range {}..={}",
                prec,
                MIN_OPER_PREC,
                MAX_OPER_PREC
            );
        }

        let assoc = Assoc::try_from(assoc.unpack_atom(self, Assoc::STRS)?)?;
        let embed_fixity = embed_fixity.unpack_atom(self, BOOLS)? == "true";

        let args = args
            .into_iter()
            .map(|arg| {
                Ok(match arg.view(self)? {
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
            .collect::<Result<Vec<_>, TermError>>()?;

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

        let rename_to = match rename_to.view(self)? {
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
            .opers
            .map
            .entry(name.clone())
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

    /// Defines one or more operators from [`arena_terms::Term`].
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
    pub fn define_opers(&mut self, term: Term) -> Result<(), TermError> {
        let ts = match term.view(self)? {
            View::List(_, ts, _) => ts.to_vec(),
            _ => {
                vec![term]
            }
        };
        for t in ts {
            self.define_oper(t)?;
        }
        Ok(())
    }

    /// Normalizes a parsed term using its operator definition.
    ///
    /// This process transforms terms according to their declared fixity,
    /// applying named default arguments and other attributes specified
    /// in the corresponding operator definition.
    ///
    /// # Parameters
    /// - `arena`: Arena used to store normalized term structures.
    /// - `term`: The parsed term to normalize.
    /// - `fixity`: Operator fixity (`fun`, `prefix`, `infix`, or `postfix`).
    /// - `op_tab_index`: Optional index into the operator definition table, if the
    ///   term corresponds to a defined operator.
    ///
    /// # Returns
    /// A normalized [`Term`] allocated in the given arena, ready for evaluation or
    /// further semantic analysis.
    ///
    /// # Errors
    /// Returns an error if normalization fails due to invalid fixity, mismatched
    /// arity, or inconsistent operator metadata.
    pub fn normalize_term(
        &mut self,
        term: Term,
        fixity: Fixity,
        op_tab_index: Option<usize>,
    ) -> Result<Term, TermError> {
        match self.get_oper(op_tab_index)[fixity] {
            Some(ref op_def) => {
                let (functor, vs) = match term.view(self)? {
                    View::Atom(_) => (term, &[] as &[Term]),
                    View::Func(_, functor, args) => {
                        if args.is_empty() {
                            bail!("invalid Func");
                        }
                        (*functor, args)
                    }
                    _ => {
                        return Ok(term);
                    }
                };
                let name = functor.atom_name(self)?;

                let n_required_args = OperDef::required_arity(fixity);
                if vs.len() < n_required_args {
                    bail!(
                        "missing {} required arguments in term {:?}",
                        n_required_args - vs.len(),
                        name
                    );
                }

                let args = &op_def.args;
                let mut xs: Vec<Option<Term>> = vec![None; args.len()];

                for (i, value) in vs.iter().enumerate() {
                    if i < n_required_args {
                        xs[i] = Some(*value);
                    } else {
                        match value.view(self)? {
                            View::Func(ar, functor, vs)
                                if vs.len() == 2 && functor.atom_name(ar)? == "=" =>
                            {
                                let arg_name = vs[0].atom_name(self)?;

                                if let Some(pos) = args.iter().position(|x| x.name == arg_name) {
                                    if xs[pos].is_none() {
                                        xs[pos] = Some(vs[1]);
                                    } else {
                                        bail!(
                                            "cannot redefine argument {:?} at position {} in {:?}",
                                            arg_name,
                                            pos,
                                            name
                                        );
                                    }
                                } else {
                                    bail!("invalid argument name {:?} in {:?}", arg_name, name);
                                }
                            }
                            _ => {
                                if xs[i].is_none() {
                                    xs[i] = Some(*value);
                                } else {
                                    bail!(
                                        "cannot redefine argument {:?} at position {} in {:?}",
                                        args[i].name,
                                        i,
                                        name
                                    );
                                }
                            }
                        }
                    }
                }

                let vs: Option<Vec<_>> = xs
                    .into_iter()
                    .enumerate()
                    .map(|(i, x)| x.or(args[i].default))
                    .collect();
                let mut vs = match vs {
                    Some(vs) => vs,
                    None => bail!("missing arguments in {:?}", name),
                };

                let rename_to = match op_def.rename_to {
                    Some(rename_to) => rename_to,
                    None => functor,
                };

                if op_def.embed_fixity {
                    vs.insert(0, self.atom(String::from(fixity)));
                }

                if vs.is_empty() {
                    Ok(rename_to)
                } else {
                    Ok(self.funcv(std::iter::once(&rename_to).chain(vs.iter()))?)
                }
            }
            None => match fixity {
                Fixity::Fun => Ok(term),
                _ => bail!("missing opdef for fixity {:?}", fixity),
            },
        }
    }

    /// Constructs the default operator definitions used by the [`TermParser`].
    ///
    /// This function populates an [`OperDefs`] table in the given [`Arena`],
    /// defining built-in operators such as `-` (prefix), `++` (infix), and `=` (infix),
    /// along with their precedence and associativity rules.
    ///
    /// ```prolog
    /// [ op(-(x), prefix, 800, right, none, false),
    ///   op(++(x, y), infix, 500, left, none, false),
    ///   op(=(x, y), infix, 100, right, none, false),
    ///   op(op(f,
    ///         =(type, fun),
    ///         =(prec, 0),
    ///         =(assoc, none),
    ///         =(rename_to, none),
    ///         =(embed_type, false)),
    ///      fun, 0, none, none, false)
    /// ]
    /// ```
    ///
    /// The resulting definitions form the standard operator environment available
    /// to the parser when no user-defined operator table is provided.
    ///
    /// # Parameters
    /// - `arena`: The [`Arena`] used for allocating operator term structures.
    ///
    /// # Returns
    /// An initialized [`OperDefs`] instance containing the default operator set.
    ///
    /// [`TermParser`]: crate::parser::TermParser
    /// [`OperDefs`]: crate::oper::OperDefs
    /// [`Arena`]: arena_terms::Arena
    /// [`aslr`]: https://crates.io/crates/parlex-gen
    pub fn define_default_opers(&mut self) -> Result<(), TermError> {
        let term = list![
            func!(
                "op";
                func!("-"; atom!("x")),
                atom!("prefix"),
                800,
                atom!("right"),
                atom!("none"),
                atom!("false"),
            ),
            func!(
                "op";
                func!("++"; atom!("x"), atom!("y")),
                atom!("infix"),
                500,
                atom!("left"),
                atom!("none"),
                atom!("false"),
            ),
            func!(
                "op";
                func!("="; atom!("x"), atom!("y")),
                atom!("infix"),
                100,
                atom!("right"),
                atom!("none"),
                atom!("false"),
            ),
            func!(
                "op";
                func!(
                    "op";
                    atom!("f"),
                    func!("="; atom!("type"), atom!("fun")),
                    func!("="; atom!("prec"), 0),
                    func!("="; atom!("assoc"), atom!("none")),
                    func!("="; atom!("rename_to"), atom!("none")),
                    func!("="; atom!("embed_type"), atom!("false")),
                ),
                atom!("fun"),
                0,
                atom!("none"),
                atom!("none"),
                atom!("false"),
            ),
            => self
        ];
        self.define_opers(term)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fixity_from_str_valid() {
        assert_eq!("fun".parse::<Fixity>().unwrap(), Fixity::Fun);
        assert_eq!("prefix".parse::<Fixity>().unwrap(), Fixity::Prefix);
        assert_eq!("infix".parse::<Fixity>().unwrap(), Fixity::Infix);
        assert_eq!("postfix".parse::<Fixity>().unwrap(), Fixity::Postfix);
    }

    #[test]
    fn fixity_from_str_invalid() {
        let err = "pre_fix".parse::<Fixity>().unwrap_err();
        assert_eq!(err.to_string(), "invalid fixity: pre_fix");
    }

    #[test]
    fn fixity_display_and_string_from() {
        assert_eq!(Fixity::Fun.to_string(), "fun");
        assert_eq!(Fixity::Prefix.to_string(), "prefix");
        assert_eq!(Fixity::Infix.to_string(), "infix");
        assert_eq!(Fixity::Postfix.to_string(), "postfix");

        let s: smartstring::alias::String = Fixity::Infix.into();
        assert_eq!(s.as_str(), "infix");
    }

    #[test]
    fn fixity_into_usize_indices() {
        assert_eq!(usize::from(Fixity::Fun), 0);
        assert_eq!(usize::from(Fixity::Prefix), 1);
        assert_eq!(usize::from(Fixity::Infix), 2);
        assert_eq!(usize::from(Fixity::Postfix), 3);
        assert_eq!(Fixity::STRS.len(), Fixity::COUNT);
    }

    #[test]
    fn assoc_from_str_valid() {
        assert_eq!("none".parse::<Assoc>().unwrap(), Assoc::None);
        assert_eq!("left".parse::<Assoc>().unwrap(), Assoc::Left);
        assert_eq!("right".parse::<Assoc>().unwrap(), Assoc::Right);
    }

    #[test]
    fn assoc_from_str_invalid() {
        let err = "center".parse::<Assoc>().unwrap_err();
        assert_eq!(err.to_string(), "invalid associativity: center");
    }

    #[test]
    fn assoc_display_and_string_from() {
        assert_eq!(Assoc::None.to_string(), "none");
        assert_eq!(Assoc::Left.to_string(), "left");
        assert_eq!(Assoc::Right.to_string(), "right");

        let s: smartstring::alias::String = Assoc::Right.into();
        assert_eq!(s.as_str(), "right");
    }

    #[test]
    fn assoc_into_usize_indices() {
        assert_eq!(usize::from(Assoc::None), 0);
        assert_eq!(usize::from(Assoc::Left), 1);
        assert_eq!(usize::from(Assoc::Right), 2);
        assert_eq!(Assoc::STRS.len(), Assoc::COUNT);
    }

    #[test]
    fn required_arity_matches_fixity() {
        assert_eq!(OperDef::required_arity(Fixity::Fun), 0);
        assert_eq!(OperDef::required_arity(Fixity::Prefix), 1);
        assert_eq!(OperDef::required_arity(Fixity::Infix), 2);
        assert_eq!(OperDef::required_arity(Fixity::Postfix), 1);
    }

    fn minimal_def(fixity: Fixity, prec: i64, assoc: Assoc) -> OperDef {
        OperDef {
            fixity,
            prec,
            assoc,
            args: Vec::new(),
            rename_to: None,
            embed_fixity: false,
        }
    }

    #[test]
    fn oper_def_tab_new_is_empty() {
        let tab = OperDefTab::new();
        assert!(!tab.is_fun());
        assert!(!tab.is_oper());
        assert!(tab.get_op_def(Fixity::Fun).is_none());
        assert!(tab.get_op_def(Fixity::Prefix).is_none());
        assert!(tab.get_op_def(Fixity::Infix).is_none());
        assert!(tab.get_op_def(Fixity::Postfix).is_none());
    }

    #[test]
    fn oper_def_tab_flags_update_correctly() {
        let mut tab = OperDefTab::new();

        // set Fun → is_fun true, is_oper still false
        tab[Fixity::Fun] = Some(minimal_def(Fixity::Fun, 0, Assoc::None));
        assert!(tab.is_fun());
        assert!(!tab.is_oper());

        // set Infix → is_oper true
        tab[Fixity::Infix] = Some(minimal_def(Fixity::Infix, 500, Assoc::Left));
        assert!(tab.is_oper());

        // get_op_def returns exactly what we put in
        let inf = tab.get_op_def(Fixity::Infix).unwrap();
        assert_eq!(inf.fixity, Fixity::Infix);
        assert_eq!(inf.prec, 500);
        assert_eq!(inf.assoc, Assoc::Left);
    }

    #[test]
    fn oper_defs_empty_behavior() {
        let arena = Arena::new();
        assert_eq!(arena.opers_len(), 0);
        assert_eq!(arena.lookup_oper("nope"), None);

        // get(None) and get(Some(0)) when empty should return the shared empty tab
        let empty1 = arena.get_oper(None);
        let empty2 = arena.get_oper(Some(0));
        assert!(!empty1.is_fun());
        assert!(!empty1.is_oper());
        assert!(!empty2.is_fun());
        assert!(!empty2.is_oper());
    }

    #[test]
    fn oper_defs_with_one_entry() {
        let mut arena = Arena::new();

        // manually create a table with one operator definition
        let mut tab = OperDefTab::new();
        let def = OperDef {
            fixity: Fixity::Infix,
            prec: 500,
            assoc: Assoc::Left,
            args: vec![
                OperArg {
                    name: "lhs".into(),
                    default: None,
                },
                OperArg {
                    name: "rhs".into(),
                    default: None,
                },
            ],
            rename_to: None,
            embed_fixity: false,
        };
        tab[Fixity::Infix] = Some(def.clone());

        arena.opers.map.insert("+".into(), tab);

        // verify map state
        assert_eq!(arena.opers_len(), 1);
        let idx = arena.lookup_oper("+").unwrap();
        let retrieved_tab = arena.get_oper(Some(idx));
        assert!(retrieved_tab.is_oper());
        assert!(!retrieved_tab.is_fun());

        let inf = retrieved_tab.get_op_def(Fixity::Infix).unwrap();
        assert_eq!(inf.fixity, Fixity::Infix);
        assert_eq!(inf.prec, 500);
        assert_eq!(inf.assoc, Assoc::Left);
        assert_eq!(inf.args.len(), 2);
        assert_eq!(inf.args[0].name, "lhs");
        assert_eq!(inf.args[1].name, "rhs");
    }
}
