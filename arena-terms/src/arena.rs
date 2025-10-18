//! Defines the [`Arena`] type, which manages allocation and interning
//! of data for [`Term`] values.
//!
//! Provides constructors, basic allocation methods, and utilities for
//! working with terms stored in the arena.

use crate::{InternalTermError, IntoTerm, OperDefs, Slice, Term, TermError, View};

/// The arena interns atoms, variables, strings, binaries, and compound terms.  
/// An `Arena` owns all memory for interned data. Terms store only indices into
/// this arena and remain valid as long as the epoch they belong to is alive.
///
/// ### Epochs
/// The arena is divided into *epochs*. Conceptually, epochs form a stack.  
/// Allocation begins in epoch `0`, which starts at offset `0` in all
/// underlying storages. At any time, the user can call `begin_epoch()`.  
/// This operation:
/// - Freezes the current epoch (recording its byte and term offsets).  
/// - Starts a new *active* epoch for subsequent allocations.  
///
/// At any point, there are `K` alive epochs, where:
/// - `K - 1` are frozen (no new data is added),  
/// - The last one is active (all new allocations go there),  
/// - and `K <= MAX_LIVE_EPOCHS` (typically very small number, currently 8).
///
/// Terms remain valid only while the epoch they were created in is alive.  
///
/// ### Truncation
/// The arena can be truncated back to a given epoch `m`, where
/// `0 <= m < MAX_LIVE_EPOCHS`:
/// - Epoch `m` and all epochs more recent than `m` are erased in O(1).  
/// - Terms from those epochs become invalid.  
/// - `truncate(0)` erases all data (synonym: `clear()`).  
/// - `truncate(current_epoch())` erases only the latest epoch  
///   (synonym: `truncate_current()`).  
///
/// Conceptually, epochs form a stack: you can `push` with `begin_epoch()`
/// and `pop` with `truncate_current()`. This makes it efficient to manage
/// temporary, scoped allocations. For example:
/// ```
/// # use arena_terms::Arena;
/// let mut arena = Arena::with_capacity(4096, 1024);
/// let epoch = arena.begin_epoch().unwrap();
/// // … build temporary terms here …
/// arena.truncate(epoch).unwrap(); // frees them all at once
/// ```
///
/// This is especially useful during iteration: each loop can create
/// short-lived terms, then discard them cleanly all at once at the end.

#[derive(Default, Clone, Debug)]
pub struct Arena {
    /// Randomly generated Arena ID
    pub(crate) arena_id: ArenaID,

    /// Index into the buffers of alive epochs.
    /// Always points to the "current" epoch (latest allocations).
    pub(crate) current_epoch: usize,

    /// Randomly generated identifiers, one per epoch.
    /// Every handle (e.g., term, func, var) that references this arena
    /// carries the epoch ID that was current at allocation time.
    /// When a handle is later resolved, the epoch ID is checked to
    /// ensure it still belongs to the same arena instance.
    pub(crate) epoch_ids: [EpochID; MAX_LIVE_EPOCHS],

    /// Storage for interned atoms, variables, strings, and binary blobs.
    /// Data are appended sequentially in the last active epoch.
    pub(crate) bytes: Vec<u8>,

    /// For each epoch, the starting offset into `bytes`.
    /// Used to "rewind" or reclaim all data belonging to an expired epoch.
    pub(crate) byte_start_by_epoch: [usize; MAX_LIVE_EPOCHS],

    /// Storage for compound terms (structured values).
    /// Terms are appended sequentially in the last active epoch.
    /// Each term is represented as a contiguous slice:
    ///   [functor_atom, arg1, arg2, …]
    /// The `Func` handle encodes both the slice’s starting index and length.
    pub(crate) terms: Vec<Term>,

    /// For each epoch, the starting index into `terms`.
    /// Used to drop/pick up all terms from an expired epoch in bulk.
    pub(crate) term_start_by_epoch: [usize; MAX_LIVE_EPOCHS],

    /// Operator definitions associated with this arena.
    pub(crate) opers: OperDefs,
}

pub const MAX_LIVE_EPOCHS: usize = 8;

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct EpochID(pub(crate) u32); // Random Epoch ID

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
pub struct ArenaID(pub(crate) u32); // Random Arena ID

#[derive(Debug, Clone, Copy)]
pub struct ArenaStats {
    pub current_epoch: EpochID,
    pub bytes_len: usize,
    pub terms_len: usize,
}

impl Arena {
    /// Create a new, empty arena with given capacities.
    pub fn with_capacity(bytes_capacity: usize, terms_capacity: usize) -> Self {
        let mut epoch_ids = [EpochID(0); MAX_LIVE_EPOCHS];
        epoch_ids[0] = EpochID(rand::random());

        Self {
            arena_id: ArenaID(rand::random()),
            current_epoch: 0,
            epoch_ids,
            bytes: Vec::with_capacity(bytes_capacity),
            byte_start_by_epoch: [0; MAX_LIVE_EPOCHS],
            terms: Vec::with_capacity(terms_capacity),
            term_start_by_epoch: [0; MAX_LIVE_EPOCHS],
            opers: OperDefs::new(),
        }
    }

    /// Create a new, empty arena with default capacities.
    pub fn new() -> Self {
        Self::with_capacity(4096, 1024)
    }

    /// Returns stats.
    pub fn stats(&self) -> ArenaStats {
        ArenaStats {
            current_epoch: self.epoch_ids[self.current_epoch],
            bytes_len: self.bytes.len(),
            terms_len: self.terms.len(),
        }
    }

    /// Returns current epoch.
    pub fn current_epoch(&self) -> EpochID {
        self.epoch_ids[self.current_epoch]
    }

    /// Freezes current epoch and begins a new one.
    pub fn begin_epoch(&mut self) -> Result<EpochID, TermError> {
        let new_epoch = self.current_epoch + 1;
        if new_epoch >= MAX_LIVE_EPOCHS {
            return Err(TermError::LiveEpochsExceeded);
        }
        self.epoch_ids[new_epoch] = EpochID(rand::random());
        self.byte_start_by_epoch[new_epoch] = self.bytes.len();
        self.term_start_by_epoch[new_epoch] = self.terms.len();
        self.current_epoch = new_epoch;
        Ok(self.epoch_ids[new_epoch])
    }

    /// Erases arena in O(1).
    /// Does not shrink the allocated capacity.
    pub fn clear(&mut self) -> Result<(), TermError> {
        self.truncate(self.epoch_ids[0])
    }

    /// Epoch `m` and all epochs more recent than `m` are erased in O(1)
    /// Does not shrink the allocated capacity.
    pub fn truncate_current(&mut self) -> Result<(), TermError> {
        self.truncate(self.epoch_ids[self.current_epoch])
    }

    /// Epoch `m` and all epochs more recent than `m` are erased in O(1)
    /// Does not shrink the allocated capacity.
    pub fn truncate(&mut self, epoch_id: EpochID) -> Result<(), TermError> {
        let epoch = self
            .epoch_index(epoch_id)
            .map_err(|_| TermError::InvalidEpoch(epoch_id))?;
        self.bytes.truncate(self.byte_start_by_epoch[epoch]);
        self.terms.truncate(self.term_start_by_epoch[epoch]);
        self.current_epoch = epoch;
        Ok(())
    }

    /// Searches epoch ID in alive epochs and returns its index.
    #[inline]
    fn epoch_index(&self, epoch_id: EpochID) -> Result<usize, InternalTermError> {
        let Some(epoch) = self.epoch_ids[..=self.current_epoch]
            .iter()
            .position(|&id| id == epoch_id)
        else {
            return Err(InternalTermError::InvalidEpoch(epoch_id));
        };
        Ok(epoch)
    }

    /// Returns an error if the term's slice's epoch is not among the alive epochs,
    /// or if the slice's index/length is inconsistent with the epoch's range.
    #[inline]
    fn verify_byte_slice(&self, slice: &Slice) -> Result<(), InternalTermError> {
        let epoch = self.epoch_index(slice.epoch_id)?;
        let epoch_start = self.byte_start_by_epoch[epoch];
        let epoch_end = if epoch == self.current_epoch {
            self.bytes.len()
        } else {
            self.byte_start_by_epoch[epoch + 1]
        };
        if (slice.index as usize) < epoch_start
            || (slice.index as usize) + (slice.len as usize) > epoch_end
        {
            return Err(InternalTermError::InvalidSlice(*slice));
        }
        Ok(())
    }

    /// Returns an error if the byte's slice's epoch is not among the alive epochs,
    /// or if the slice's index/length is inconsistent with the epoch's range.
    #[inline]
    fn verify_term_slice(&self, slice: &Slice) -> Result<(), InternalTermError> {
        let epoch = self.epoch_index(slice.epoch_id)?;
        let epoch_start = self.term_start_by_epoch[epoch];
        let epoch_end = if epoch == self.current_epoch {
            self.terms.len()
        } else {
            self.term_start_by_epoch[epoch + 1]
        };
        if (slice.index as usize) < epoch_start
            || (slice.index as usize) + (slice.len as usize) > epoch_end
        {
            return Err(InternalTermError::InvalidSlice(*slice));
        }
        Ok(())
    }

    /// Convert a `value` into `Term`.
    #[inline]
    pub fn term<'a, T: IntoTerm>(&'a mut self, value: T) -> Term {
        value.into_term(self)
    }

    /// Construct a new integer term.  The full 64 bit two's complement
    /// representation of `i` is stored in the payload.  No truncation
    /// occurs.
    #[inline]
    pub fn int(&mut self, i: impl Into<i64>) -> Term {
        Term::int(i)
    }

    /// Construct a new floating point term.  The full 64 bit IEEE‑754
    /// bit pattern is stored in the payload without truncation.
    #[inline]
    pub fn real(&mut self, r: impl Into<f64>) -> Term {
        Term::real(r)
    }

    /// Construct a new date term representing a Unix epoch in
    /// milliseconds.
    #[inline]
    pub fn date(&mut self, ms: impl Into<i64>) -> Term {
        Term::date(ms)
    }

    /// Construct or intern an atom into the arena and produce a term
    /// referencing it.  Small atom names (≤14 bytes of UTF‑8) are
    /// inlined directly into the handle; longer names are interned
    /// into the arena and referenced by index and length.
    #[inline]
    pub fn atom(&mut self, name: impl AsRef<str>) -> Term {
        Term::atom(self, name)
    }

    /// Construct or intern a variable into the arena and produce a
    /// term referencing it.  Small variable names (≤14 bytes) are
    /// inlined directly into the handle; longer names are interned in
    /// the arena and referenced by index.
    #[inline]
    pub fn var(&mut self, name: impl AsRef<str>) -> Term {
        Term::var(self, name)
    }

    /// Construct or intern a UTF‑8 string into the arena and produce a
    /// term referencing it.  Strings longer than 14 bytes are interned
    /// in the arena; shorter strings are inlined.  Invalid UTF‑8 will
    /// result in an error.
    #[inline]
    pub fn str(&mut self, s: impl AsRef<str>) -> Term {
        Term::str(self, s)
    }

    /// Construct or intern a binary blob into the arena and produce a
    /// term referencing it.  Blobs longer than 14 bytes are interned
    /// in the arena; shorter blobs are inlined.
    #[inline]
    pub fn bin(&mut self, bytes: impl AsRef<[u8]>) -> Term {
        Term::bin(self, bytes)
    }

    /// Construct a new compound term by interning the functor and
    /// arguments in the arena.  The returned term references a slice
    /// in the arena's term storage consisting of the functor atom as
    /// the first entry followed by the argument handles.  A functor of
    /// arity zero results in an atom.
    #[inline]
    pub fn func(
        &mut self,
        functor: impl AsRef<str>,
        args: impl IntoIterator<Item = impl IntoTerm>,
    ) -> Term {
        Term::func(self, functor, args)
    }

    /// Construct a new compound term by interning the functor and its arguments
    /// into the arena as a sequence of terms (functor first, then arguments).
    /// A functor with no arguments yields the atom itself.  Errors if
    /// no functor is provided or if the first term is not an atom.
    #[inline]
    pub fn funcv(
        &mut self,
        terms: impl IntoIterator<Item = impl IntoTerm>,
    ) -> Result<Term, TermError> {
        Term::funcv(self, terms)
    }

    /// Constructs a new list. A list is represented internally as an
    /// array of terms. If `terms` is empty, returns `nil`.
    #[inline]
    pub fn list(&mut self, terms: impl IntoIterator<Item = impl IntoTerm>) -> Term {
        Term::list(self, terms)
    }

    /// Constructs a new improper list. An improper list is represented as
    /// a list and additional argument. If `terms` is empty, returns `nil`.
    #[inline]
    pub fn listc(
        &mut self,
        terms: impl IntoIterator<Item = impl IntoTerm>,
        tail: impl IntoTerm,
    ) -> Term {
        Term::listc(self, terms, tail)
    }

    /// Constructs a new tuple. A tuple is represented internally as an array
    /// of terms.
    #[inline]
    pub fn tuple(&mut self, terms: impl IntoIterator<Item = impl IntoTerm>) -> Term {
        Term::tuple(self, terms)
    }

    /// Constant representing the zero‑arity tuple (unit).  Internally
    /// this is the atom `"unit"` encoded as a small atom.  It may
    /// be copied freely and does not depend on any arena.
    pub const UNIT: Term = Term::UNIT;

    /// Constant representing the empty list (nil).  Internally this is
    /// the atom `"nil"` encoded as a small atom.  It may be copied
    /// freely and does not depend on any arena.
    pub const NIL: Term = Term::NIL;

    /// Returns the name of a compound term, atom, or variable.
    /// Use [`unpack_atom`], [`unpack_func`], or [`unpack_var`]
    /// to ensure the term is of a specific kind.
    #[inline]
    pub fn name<'a>(&'a self, term: &'a Term) -> Result<&'a str, TermError> {
        match self.view(term)? {
            View::Var(name) | View::Atom(name) => Ok(name),
            View::Func(ar, functor, _) => Ok(functor.atom_name(ar)?),
            _ => Err(TermError::UnexpectedKind {
                expected: "var, atom, func",
                found: term.kind_name(),
            }),
        }
    }

    /// Returns the name of an atom,
    #[inline]
    pub fn atom_name<'a>(&'a self, term: &'a Term) -> Result<&'a str, TermError> {
        self.unpack_atom(term, &[])
    }

    /// Returns the name of a variable.
    #[inline]
    pub fn var_name<'a>(&'a self, term: &'a Term) -> Result<&'a str, TermError> {
        self.unpack_var(term, &[])
    }

    /// Returns the name of a compund term.
    #[inline]
    pub fn func_name<'a>(&'a self, term: &'a Term) -> Result<&'a str, TermError> {
        let (functor, _) = self.unpack_func_any(term, &[])?;
        self.atom_name(functor)
    }

    /// Returns the value if `term` is an integer, otherwise an error.
    #[inline]
    pub fn unpack_int(&self, term: &Term) -> Result<i64, TermError> {
        match self.view(term)? {
            View::Int(v) => Ok(v),
            _ => Err(TermError::UnexpectedKind {
                expected: "int",
                found: term.kind_name(),
            }),
        }
    }

    /// Returns the value if `term` is a real, otherwise an error.
    #[inline]
    pub fn unpack_real(&self, term: &Term) -> Result<f64, TermError> {
        match self.view(term)? {
            View::Real(v) => Ok(v),
            _ => Err(TermError::UnexpectedKind {
                expected: "real",
                found: term.kind_name(),
            }),
        }
    }

    /// Returns the value if `term` is a date, otherwise an error.
    #[inline]
    pub fn unpack_date(&self, term: &Term) -> Result<i64, TermError> {
        match self.view(term)? {
            View::Date(v) => Ok(v),
            _ => Err(TermError::UnexpectedKind {
                expected: "date",
                found: term.kind_name(),
            }),
        }
    }

    /// Returns the string slice if `term` is a string, otherwise an error.
    #[inline]
    pub fn unpack_str<'a>(&'a self, term: &'a Term) -> Result<&'a str, TermError> {
        match self.view(term)? {
            View::Str(v) => Ok(v),
            _ => Err(TermError::UnexpectedKind {
                expected: "str",
                found: term.kind_name(),
            }),
        }
    }

    /// Returns the slice if `term` is a binary blob, otherwise an error.
    #[inline]
    pub fn unpack_bin<'a>(&'a self, term: &'a Term) -> Result<&'a [u8], TermError> {
        match self.view(term)? {
            View::Bin(v) => Ok(v),
            _ => Err(TermError::UnexpectedKind {
                expected: "bin",
                found: term.kind_name(),
            }),
        }
    }

    /// Returns the name if `term` is an atom, otherwise an error.
    #[inline]
    pub fn unpack_atom<'a>(
        &'a self,
        term: &'a Term,
        allowed_names: &[&str],
    ) -> Result<&'a str, TermError> {
        match self.view(term)? {
            View::Atom(name) => {
                if !allowed_names.is_empty() && !allowed_names.contains(&name) {
                    return Err(TermError::UnexpectedName(*term));
                }
                Ok(name)
            }
            _ => Err(TermError::UnexpectedKind {
                expected: "atom",
                found: term.kind_name(),
            }),
        }
    }

    /// Returns the name if `term` is a variable, otherwise an error.
    #[inline]
    pub fn unpack_var<'a>(
        &'a self,
        term: &'a Term,
        allowed_names: &[&str],
    ) -> Result<&'a str, TermError> {
        match self.view(term)? {
            View::Var(name) => {
                if !allowed_names.is_empty() && !allowed_names.contains(&name) {
                    return Err(TermError::UnexpectedName(*term));
                }
                Ok(name)
            }
            _ => Err(TermError::UnexpectedKind {
                expected: "var",
                found: term.kind_name(),
            }),
        }
    }

    /// Returns the name and arguments if `term` is a compound term of any arity
    /// or an atom and its name is in `allowed_names` (or if `allowed_names` is empty),
    /// otherwise returns an error.
    #[inline]
    pub fn unpack_func_any<'a>(
        &'a self,
        term: &'a Term,
        allowed_names: &[&str],
    ) -> Result<(&'a Term, &'a [Term]), TermError> {
        match self.view(term)? {
            View::Atom(name) => {
                if !allowed_names.is_empty() && !allowed_names.contains(&name) {
                    return Err(TermError::UnexpectedName(*term));
                }
                Ok((term, &[] as &[Term]))
            }
            View::Func(_, functor, args) => {
                if args.is_empty() {
                    return Err(TermError::InvalidTerm(*term));
                }
                if !allowed_names.is_empty() {
                    let name = self.atom_name(functor)?;
                    if !allowed_names.contains(&name) {
                        return Err(TermError::UnexpectedName(*term));
                    }
                }
                Ok((functor, args))
            }
            _ => Err(TermError::UnexpectedKind {
                expected: "func",
                found: term.kind_name(),
            }),
        }
    }

    /// Returns the name and arguments if `term` is a compound term of arity `ARITY`
    /// (or an atom if `ARITY == 0`) and its name is in `allowed_names` (or if `allowed_names` is empty),
    /// otherwise returns an error.
    #[inline]
    pub fn unpack_func<'a, const ARITY: usize>(
        &'a self,
        term: &'a Term,
        allowed_names: &[&str],
    ) -> Result<(&'a Term, [Term; ARITY]), TermError> {
        let (functor, args) = self.unpack_func_any(term, allowed_names)?;
        if args.len() != ARITY {
            return Err(TermError::UnexpectedArity {
                expected: ARITY,
                found: args.len(),
            });
        }
        let arr: [_; ARITY] = args.try_into().unwrap();
        return Ok((functor, arr));
    }

    /// Returns the slice with list elements and the tail if `term` is a list,
    /// otherwise returns an error.
    #[inline]
    pub fn unpack_list<'a>(&'a self, term: &'a Term) -> Result<(&'a [Term], &'a Term), TermError> {
        match self.view(term)? {
            View::Atom(_) if term == &Term::NIL => Ok((&[], &Term::NIL)),
            View::List(_, terms, tail) => Ok((terms, tail)),
            _ => Err(TermError::UnexpectedKind {
                expected: "list",
                found: term.kind_name(),
            }),
        }
    }

    /// Returns the slice with tuple elements if `term` is a tuple of any arity,
    /// otherwise returns an error.
    #[inline]
    pub fn unpack_tuple_any<'a>(&'a self, term: &'a Term) -> Result<&'a [Term], TermError> {
        match self.view(term)? {
            View::Atom(_) if *term == Term::UNIT => Ok(&[]),
            View::Tuple(_, terms) => Ok(terms),
            _ => Err(TermError::UnexpectedKind {
                expected: "tuple",
                found: term.kind_name(),
            }),
        }
    }

    /// Returns the tuple elements if `term` is a tuple of arity `ARITY`,
    /// otherwise returns an error.
    #[inline]
    pub fn unpack_tuple<const ARITY: usize>(
        &self,
        term: &Term,
    ) -> Result<[Term; ARITY], TermError> {
        let terms = self.unpack_tuple_any(term)?;
        if terms.len() != ARITY {
            return Err(TermError::UnexpectedArity {
                expected: ARITY,
                found: terms.len(),
            });
        }
        let arr: [_; ARITY] = terms.try_into().unwrap();
        return Ok(arr);
    }

    /// Intern a UTF‑8 string into the arena and return its slice
    /// descriptor.  Strings are stored in a contiguous bump vector.
    #[inline]
    pub(crate) fn intern_str(&mut self, s: &str) -> Slice {
        let index = self.bytes.len();
        self.bytes.extend_from_slice(s.as_bytes());
        let len = s.len();
        Slice {
            epoch_id: self.epoch_ids[self.current_epoch],
            index: index as u32,
            len: len as u32,
        }
    }

    /// Intern a binary blob into the arena and return its slice descriptor.
    #[inline]
    pub(crate) fn intern_bytes(&mut self, bytes: &[u8]) -> Slice {
        let index = self.bytes.len();
        self.bytes.extend_from_slice(bytes);
        let len = bytes.len();
        Slice {
            epoch_id: self.epoch_ids[self.current_epoch],
            index: index as u32,
            len: len as u32,
        }
    }

    /// Intern a compound term slice (functor + args) into the term arena.
    #[inline]
    pub(crate) fn intern_func(
        &mut self,
        functor: Term,
        args: impl IntoIterator<Item = impl IntoTerm>,
    ) -> Slice {
        let index = self.terms.len();
        self.terms.push(functor);
        for x in args {
            let t = x.into_term(self);
            self.terms.push(t);
        }
        let len = self.terms.len() - index;
        Slice {
            epoch_id: self.epoch_ids[self.current_epoch],
            index: index as u32,
            len: len as u32,
        }
    }

    /// Intern a seq term slice into the term arena.
    #[inline]
    pub(crate) fn intern_seq(&mut self, terms: impl IntoIterator<Item = impl IntoTerm>) -> Slice {
        let index = self.terms.len();
        for x in terms {
            let t = x.into_term(self);
            self.terms.push(t);
        }
        let len = self.terms.len() - index;
        Slice {
            epoch_id: self.epoch_ids[self.current_epoch],
            index: index as u32,
            len: len as u32,
        }
    }

    /// Intern a seq term slice plus tail into the term arena.
    #[inline]
    pub(crate) fn intern_seq_plus_one(
        &mut self,
        terms: impl IntoIterator<Item = impl IntoTerm>,
        tail: impl IntoTerm,
    ) -> Slice {
        let index = self.terms.len();
        for x in terms {
            let t = x.into_term(self);
            self.terms.push(t);
        }
        let t = tail.into_term(self);
        self.terms.push(t);
        let len = self.terms.len() - index;
        Slice {
            epoch_id: self.epoch_ids[self.current_epoch],
            index: index as u32,
            len: len as u32,
        }
    }

    /// Borrow a slice of bytes stored in the arena.
    /// should not be called directly by users; instead use
    /// [`Term::view`].
    #[inline]
    pub(crate) fn byte_slice<'a>(&'a self, slice: &Slice) -> Result<&'a [u8], InternalTermError> {
        self.verify_byte_slice(slice)?;
        Ok(&self.bytes[(slice.index as usize)..((slice.index + slice.len) as usize)])
    }

    /// Borrow a slice of terms comprising a compound term.
    #[inline]
    pub(crate) fn term_slice<'a>(&'a self, slice: &Slice) -> Result<&'a [Term], InternalTermError> {
        self.verify_term_slice(slice)?;
        Ok(&self.terms[(slice.index as usize)..((slice.index + slice.len) as usize)])
    }
}
