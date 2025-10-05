// This module defines LR(0) item machinery, FIRST/FOLLOW computations,
// and SLR(1) parse table construction.

use std::collections::BTreeSet;
use std::io::{self, Write};

/// Represents an LR(0) item consisting of a production index and a dot position.
///
/// Each item corresponds to a production with a marker (the *dot*) indicating
/// how much of the right-hand side has been recognized during parsing.
///
/// For example, if production `E → E + T` is partially parsed as `E → E • + T`,
/// the `Item` stores the production index for `E → E + T` and a dot position
/// indicating the marker is after the first symbol.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Item {
    /// The index of the production in the grammar.
    pub prod: usize,

    /// The position of the dot within the production’s right-hand side.
    pub dot: usize,
}

/// A set of LR(0) items
pub type ItemSet = BTreeSet<Item>;

/// The canonical collection of LR(0) item sets.
///
/// Represents the set of all distinct item sets constructed during
/// canonical collection generation in SLR(1) parser construction.
/// The canonical collection of item-sets
pub type ItemSetSet = BTreeSet<ItemSet>;

/// Computes the LR(0) *closure* of a set of items.
///
/// For each item in the input set, this function adds new items corresponding
/// to productions of the nonterminal immediately following the dot position,
/// repeating until no new items are added.
///
/// # Parameters
/// - `items`: The initial set of LR(0) items.
/// - `prods`: A list of productions, where each production is represented as a
///   sequence of symbol indices (with the left-hand side at index `0`).
/// - `n_nonterm`: The number of nonterminal symbols in the grammar.
///   Symbols with indices `< n_nonterm` are treated as nonterminals.
///
/// # Returns
/// The full closure set containing the original and newly added items.
///
/// # Example
/// ```text
/// Given items for `S' → • S`
/// and productions for `S → A`, `A → a`,
/// this function will add items for each production of `S`.
/// ```
///
/// # Notes
/// This implementation operates purely on integer-based grammar encodings.
pub fn closure(items: &ItemSet, prods: &[Vec<usize>], n_nonterm: usize) -> ItemSet {
    let mut c = items.clone();
    let mut inserted = true;
    while inserted {
        inserted = false;
        // Iterate over a snapshot to avoid borrowing issues
        for item in c.clone().into_iter() {
            // If dot position points to a symbol
            if item.dot < prods[item.prod].len() {
                let t = prods[item.prod][item.dot];
                // If it's a non-terminal, add its productions
                if t < n_nonterm {
                    for (j, p) in prods.iter().enumerate() {
                        if p[0] == t {
                            let new_item = Item { prod: j, dot: 1 };
                            if c.insert(new_item.clone()) {
                                inserted = true;
                            }
                        }
                    }
                }
            }
        }
    }
    c
}

/// Computes the LR(0) *goto* function for a given item set and grammar symbol.
///
/// Produces a new item set containing items advanced past `sym`,
/// then computes and returns its closure.
///
/// # Parameters
/// - `items`: The current set of LR(0) items.
/// - `sym`: The grammar symbol to transition on (by index).
/// - `prods`: The list of grammar productions, represented as symbol index vectors.
/// - `n_nonterm`: The number of nonterminal symbols in the grammar.
///
/// # Returns
/// The closure of all items reachable from `items` on the given symbol.
///
/// # Example
/// Transitioning from items with `S → • A` on symbol `A` produces
/// items with `S → A •`, followed by closure expansion.
pub fn goto(items: &ItemSet, sym: usize, prods: &[Vec<usize>], n_nonterm: usize) -> ItemSet {
    let mut moved = ItemSet::new();
    for item in items {
        let p = &prods[item.prod];
        if item.dot < p.len() && p[item.dot] == sym {
            moved.insert(Item {
                prod: item.prod,
                dot: item.dot + 1,
            });
        }
    }
    closure(&moved, prods, n_nonterm)
}

/// Constructs the canonical collection of LR(0) item sets.
///
/// Iteratively applies the [`closure`] and [`goto`] functions to generate
/// all distinct item sets reachable from the start production.
/// This process forms the foundation of LR(0), SLR(1), and LR(1)
/// parser table construction.
///
/// # Parameters
/// - `prods`: Grammar productions, represented as symbol index vectors.
/// - `n_nonterm`: Number of nonterminal symbols in the grammar.
/// - `n_term`: Number of terminal symbols in the grammar.
///
/// # Returns
/// A canonical collection of LR(0) item sets (`ItemSetSet`).
///
/// # Example
/// The first item set typically starts with the augmented production
/// `S' → • S`, from which all other states are derived.
pub fn construct_set(prods: &[Vec<usize>], n_nonterm: usize, n_term: usize) -> ItemSetSet {
    let mut c = ItemSetSet::new();
    // Start closure on initial item (prod 0, dot at 1)
    let start0 = ItemSet::from([Item { prod: 0, dot: 1 }]);
    c.insert(closure(&start0, prods, n_nonterm));
    let mut changed = true;
    while changed {
        changed = false;
        for state in c.clone().into_iter() {
            for sym in 0..(n_nonterm + n_term) {
                let nxt = goto(&state, sym, prods, n_nonterm);
                if !nxt.is_empty() && c.insert(nxt) {
                    changed = true;
                }
            }
        }
    }
    c
}

/// Writes the canonical collection of item sets to an output stream.
///
/// Each state and its corresponding items are written in a compact
/// human-readable form for debugging or analysis. The output format
/// includes markers for dot positions and symbol names.
///
/// # Parameters
/// - `out`: The output writer (e.g., file, buffer, or stdout).
/// - `c`: The canonical collection of item sets to display.
/// - `prods`: The grammar productions as symbol index vectors.
/// - `tokens`: Symbol names (terminals and nonterminals) indexed by symbol ID.
///
/// # Returns
/// Returns `Ok(())` on success or an [`io::Error`] if writing fails.

pub fn write_set<W: Write>(
    out: &mut W,
    c: &ItemSetSet,
    prods: &[Vec<usize>],
    tokens: &[String],
) -> io::Result<()> {
    writeln!(out, "CS,{}\n", c.len())?;
    for (i, state) in c.iter().enumerate() {
        for item in state {
            write!(out, "C,{},", i)?;
            let p = &prods[item.prod];
            for (j, t) in p.iter().enumerate() {
                if j == item.dot {
                    write!(out, ". ")?;
                }
                write!(out, "{} ", tokens[*t])?;
                if j == 0 {
                    write!(out, "-> ")?;
                }
            }
            if p.len() == item.dot {
                write!(out, ". ")?;
            }
            writeln!(out, "")?;
        }
        writeln!(out, "")?;
    }
    Ok(())
}

/// Writes the grammar productions to an output stream.
///
/// Each production is written in a compact, human-readable format,
/// showing the left-hand side (LHS) and right-hand side (RHS) symbols
/// using their string labels.
///
/// This function is primarily used for debugging, grammar inspection,
/// or as part of parser table generation output.
///
/// # Parameters
/// - `out`: The output writer (e.g., file, buffer, or stdout).
/// - `prods`: The list of productions, represented as symbol index vectors.
///   The first element of each vector is the left-hand side symbol.
/// - `tokens`: Symbol names (terminals and nonterminals) indexed by symbol ID.
///
/// # Returns
/// Returns `Ok(())` on success or an [`io::Error`] if writing fails.
///
/// # Output Format
/// ```text
/// PS,<number of productions>
///
/// P,<index>,<LHS> -> <RHS symbols>
/// ```
pub fn write_prods<W: Write>(
    out: &mut W,
    prods: &[Vec<usize>],
    tokens: &[String],
) -> io::Result<()> {
    writeln!(out, "PS,{}\n", prods.len())?;
    for (i, prod) in prods.iter().enumerate() {
        write!(out, "P,{},", i)?;
        for (j, t) in prod.iter().enumerate() {
            write!(out, "{} ", tokens[*t])?;
            if j == 0 {
                write!(out, "-> ")?;
            }
        }
        writeln!(out)?;
    }
    Ok(())
}

/// Writes FIRST or FOLLOW sets to the output stream.
///
/// If `nullable` is provided, prints FIRST sets (including `` `empty' `` for nullable symbols);
/// otherwise, prints FOLLOW sets. Each set is formatted in a compact, readable form.
///
/// # Parameters
/// - `out`: Output writer (e.g., file or buffer).
/// - `vs`: FIRST or FOLLOW sets for each grammar symbol.
/// - `nullable`: Optional nullability flags (for FIRST sets).
/// - `tokens`: Symbol names indexed by ID.
pub fn write_fstflw<W: Write>(
    out: &mut W,
    vs: &[BTreeSet<usize>],
    nullable: Option<&[bool]>,
    tokens: &[String],
) -> io::Result<()> {
    let (label, nullable) = match nullable {
        Some(nullable) => ("FIRST", nullable.to_vec()),
        None => ("FOLLOW", vec![false; vs.len()]),
    };

    for (sym, set) in vs.iter().enumerate() {
        let dname = format!("${}", sym);
        let name = tokens.get(sym).unwrap_or(&dname);

        write!(out, "{},{},{{", label, name)?;

        if nullable[sym] {
            write!(out, "`empty', ")?;
        }

        for &t in set {
            let dname = format!("${}", t);
            let tname = tokens.get(t).unwrap_or(&dname);
            write!(out, "{}, ", tname)?;
        }

        writeln!(out, "}}")?;
    }

    Ok(())
}

/// Computes FIRST sets and nullability for all grammar symbols.
///
/// Iteratively determines which terminals can begin each nonterminal’s derivations
/// and which symbols can derive the empty string.
///
/// # Parameters
/// - `prods`: Grammar productions, with the LHS at index `0`.
/// - `n_nonterm`: Number of nonterminal symbols.
/// - `n_term`: Number of terminal symbols.
///
/// # Returns
/// A tuple containing:
/// - A vector of FIRST sets (one per symbol).
/// - A vector of booleans marking nullable symbols.
pub fn first_sets(
    prods: &[Vec<usize>],
    n_nonterm: usize,
    n_term: usize,
) -> (Vec<BTreeSet<usize>>, Vec<bool>) {
    let n_sym = n_nonterm + n_term;
    let mut first: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); n_sym];
    let mut nullable = vec![false; n_sym];
    // Terminals: FIRST(t) = {t}
    for t in n_nonterm..n_sym {
        first[t].insert(t);
    }
    let mut changed = true;
    while changed {
        changed = false;
        for prod in prods {
            let lhs = prod[0];
            if prod.len() == 1 {
                // ε-production
                if !nullable[lhs] {
                    nullable[lhs] = true;
                    changed = true;
                }
            } else {
                let mut all_nullable = true;
                for &sym in &prod[1..] {
                    // Clone FIRST(sym) to avoid simultaneous borrow
                    let first_sym = first[sym].clone();
                    for f in first_sym {
                        if first[lhs].insert(f) {
                            changed = true;
                        }
                    }
                    if !nullable[sym] {
                        all_nullable = false;
                        break;
                    }
                }
                if all_nullable && !nullable[lhs] {
                    nullable[lhs] = true;
                    changed = true;
                }
            }
        }
    }
    (first, nullable)
}

/// Computes FOLLOW sets for all nonterminal symbols.
///
/// Determines which terminals can appear immediately after each nonterminal
/// in valid derivations, using the provided FIRST sets and nullability information.
///
/// # Parameters
/// - `prods`: Grammar productions, with the LHS at index `0`.
/// - `n_nonterm`: Number of nonterminal symbols.
/// - `n_term`: Number of terminal symbols.
/// - `start_sym`: Index of the start symbol (receives end-of-input marker `$`).
/// - `first`: Precomputed FIRST sets for all symbols.
/// - `nullable`: Boolean flags indicating which symbols are nullable.
///
/// # Returns
/// A vector of FOLLOW sets, one per nonterminal.
pub fn follow_sets(
    prods: &[Vec<usize>],
    n_nonterm: usize,
    n_term: usize,
    start_sym: usize,
    first: &Vec<BTreeSet<usize>>,
    nullable: &Vec<bool>,
) -> Vec<BTreeSet<usize>> {
    let eos = n_nonterm + n_term - 1;
    let mut follow: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); n_nonterm];
    // EOF marker at start symbol
    follow[start_sym].insert(eos);
    let mut changed = true;
    while changed {
        changed = false;
        for prod in prods {
            let lhs = prod[0];
            let rhs = &prod[1..];
            for i in 0..rhs.len() {
                let b = rhs[i];
                if b < n_nonterm {
                    // Compute FIRST of beta
                    let mut beta_nullable = true;
                    let mut first_beta = BTreeSet::new();
                    for &sym in &rhs[i + 1..] {
                        let first_sym = first[sym].clone();
                        for f in first_sym {
                            first_beta.insert(f);
                        }
                        if !nullable[sym] {
                            beta_nullable = false;
                            break;
                        }
                    }
                    // Add FIRST(beta) to FOLLOW(b)
                    for &f in &first_beta {
                        if follow[b].insert(f) {
                            changed = true;
                        }
                    }
                    // If beta nullable, add FOLLOW(lhs) to FOLLOW(b)
                    if beta_nullable {
                        let follow_lhs = follow[lhs].clone();
                        for f in follow_lhs {
                            if follow[b].insert(f) {
                                changed = true;
                            }
                        }
                    }
                }
            }
        }
    }
    follow
}

/// Finds the index of a given item set within the canonical collection.
///
/// Searches for an exact match of `target` in `c` and returns its index if found.
///
/// # Parameters
/// - `c`: The canonical collection of LR(0) item sets.
/// - `target`: The item set to locate.
///
/// # Returns
/// The index of the matching state, or `None` if not found.
fn find_state(c: &ItemSetSet, target: &ItemSet) -> Option<usize> {
    for (i, st) in c.iter().enumerate() {
        if st == target {
            return Some(i);
        }
    }
    None
}

/// Represents the type of parser action.
///
/// Each variant corresponds to a possible action in an LR parsing table,
/// such as shifting, reducing, or accepting input.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ActTyp {
    /// Error or invalid action.
    _Error = 0,
    /// Accept action — indicates successful parse completion.
    Accept = 1,
    /// Shift action — pushes a new state onto the stack.
    Shift = 2,
    /// Reduce action — applies a grammar production.
    Reduce = 3,
    /// Ambiguity marker (internal use).
    _Ambig = 4,
    /// Goto action — transitions to a nonterminal state.
    Goto = 5,
}

/// Implementation of [`ActTyp`] methods.
///
/// Provides utility functions for representing parser action types.
impl ActTyp {
    /// Returns the string name of this action type.
    pub fn to_str(self) -> &'static str {
        match self {
            ActTyp::_Error => "Error",
            ActTyp::Accept => "Accept",
            ActTyp::Shift => "Shift",
            ActTyp::Reduce => "Reduce",
            ActTyp::_Ambig => "Ambig",
            ActTyp::Goto => "Goto",
        }
    }
}

/// A parse action
/// Represents a parser action entry.
///
/// Each action combines a type ([`ActTyp`]) with an associated value —
/// such as a state index, production index, or target symbol.
///
/// Used in LR parsing tables to drive state transitions.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Act {
    /// The action type (e.g., Shift, Reduce, Goto).
    pub typ: ActTyp,
    /// The numeric value associated with the action
    /// (e.g., target state or production index).
    pub val: usize,
}

/// Implementation of [`Act`] methods.
///
/// Provides constructors and formatting helpers for parser actions.
impl Act {
    /// Creates a new [`Act`] with the given type and value.
    ///
    /// # Parameters
    /// - `typ`: The action type (e.g., [`ActTyp::Shift`], [`ActTyp::Reduce`]).
    /// - `val`: The numeric value associated with the action,
    ///   such as a state or production index.
    pub fn new(typ: ActTyp, val: usize) -> Self {
        Act { typ, val }
    }

    /// Converts the action’s value into a readable string representation.
    ///
    /// Used for debugging or code generation. Formats the value according
    /// to the action type (e.g., `"StateID(3)"`, `"ProdID::Expr1"`).
    ///
    /// # Parameters
    /// - `prod_enums`: A list of production enum names used for reduce actions.
    ///
    /// # Returns
    /// A formatted string representation, or `None` for actions
    /// without a value (`Error`, `Accept`).
    pub fn val_to_string(&self, prod_enums: &[String]) -> Option<String> {
        match self.typ {
            ActTyp::_Error => None,
            ActTyp::Accept => None,
            ActTyp::Shift => Some(format!("StateID({})", self.val)),
            ActTyp::Reduce => Some(format!("ProdID::{}", prod_enums[self.val])),
            ActTyp::_Ambig => Some(format!("AmbigID({})", self.val)),
            ActTyp::Goto => Some(format!("StateID({})", self.val)),
        }
    }
}

/// Represents an SLR(1) parse table.
///
/// The table is organized as a two-dimensional vector:
/// - **Rows** correspond to parser states.
/// - **Columns** correspond to grammar symbols (terminals and nonterminals).
///
/// Each cell contains a set of [`Act`] values representing possible
/// parser actions (e.g., shift, reduce, goto).
///
/// Used internally to generate and serialize SLR(1) parsing tables.
pub type Tab = Vec<Vec<BTreeSet<Act>>>;

/// Constructs an SLR(1) parse table from the canonical collection.
///
/// Builds the full action/goto table using the canonical LR(0) item sets
/// and the FOLLOW sets of the grammar. Each cell in the resulting table
/// contains zero or more parser actions (`Shift`, `Reduce`, `Goto`, `Accept`).
///
/// # Parameters
/// - `c`: The canonical collection of LR(0) item sets.
/// - `flw`: The FOLLOW sets for each nonterminal.
/// - `prods`: Grammar productions, with the LHS at index `0`.
/// - `n_nonterm`: Number of nonterminal symbols.
/// - `n_term`: Number of terminal symbols.
///
/// # Returns
/// An [`Tab`] representing the constructed SLR(1) parse table.
///
/// # Notes
/// - Shift actions are added for transitions on terminals.
/// - Reduce actions are added for completed items using FOLLOW sets.
/// - Goto entries are generated for transitions on nonterminals.
pub fn construct_slr(
    c: &ItemSetSet,
    flw: &[BTreeSet<usize>],
    prods: &[Vec<usize>],
    n_nonterm: usize,
    n_term: usize,
) -> Tab {
    let size = c.len();
    let mut tab: Tab = Vec::with_capacity(size);
    tab.resize(size, Vec::new());
    for row in tab.iter_mut() {
        row.resize(n_nonterm + n_term, BTreeSet::new());
    }

    // Fill GOTO for non-terminals
    for sym in 1..(n_nonterm) {
        for (state, ssi) in c.iter().enumerate() {
            let nxt = goto(ssi, sym, prods, n_nonterm);
            if let Some(ns) = find_state(c, &nxt) {
                tab[state][sym].insert(Act::new(ActTyp::Goto, ns));
            }
        }
    }

    // Fill SHIFT and REDUCE and ACCEPT for terminals
    for sym in n_nonterm..(n_nonterm + n_term) {
        for (state, ssi) in c.iter().enumerate() {
            for item in ssi {
                let p = &prods[item.prod];
                if item.dot < p.len() && p[item.dot] == sym {
                    let nxt = goto(ssi, sym, prods, n_nonterm);
                    if let Some(ns) = find_state(c, &nxt) {
                        tab[state][sym].insert(Act::new(ActTyp::Shift, ns));
                    }
                } else if item.dot == p.len() {
                    let ltok = p[0];
                    if ltok == 0 && p.len() == 2 && p[1] == 1 {
                        // Accept on EOF token (last column)
                        tab[state][n_nonterm + n_term - 1].insert(Act::new(ActTyp::Accept, 0));
                    } else if ltok < flw.len() {
                        for &t in &flw[ltok] {
                            tab[state][t].insert(Act::new(ActTyp::Reduce, item.prod));
                        }
                    }
                }
            }
        }
    }
    tab
}
