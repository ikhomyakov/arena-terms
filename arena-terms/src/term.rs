//! Defines the core [`Term`] type and related constructors.
//!
//! Provides a compact representation for Prolog-like terms
//! and basic utilities for creating and inspecting them.

use crate::{Arena, EpochID, TermError};
use core::fmt;
use smartstring::alias::String;
use std::borrow::Cow;

// The following type definitions describe the internal representation
// of a term.  Rather than packing data into a single integer we use
// a tagged enum to store the various kinds of terms.  Each variant
// carries its associated data directly, for example a 64 bit integer
// for numeric types or a small inline buffer for short atoms and
// variables.  Long names or sequences store an index and length into
// the appropriate arena.

#[derive(Debug, Copy, Clone, PartialEq, PartialOrd)]
pub(crate) struct TinyArray {
    pub(crate) bytes: [u8; 14],
    pub(crate) len: u8,
}

#[derive(Debug, Copy, Clone, PartialEq, PartialOrd)]
pub(crate) struct Slice {
    pub(crate) epoch_id: EpochID,
    pub(crate) index: u32,
    pub(crate) len: u32,
}

/// Internal handle describing the kind of a term and storing its data.
///
/// Each variant stores the associated value directly.  The `repr(u8)`
/// attribute ensures the discriminant occupies a single byte, which
/// together with the payloads yields a `Term` size of 16 bytes on
/// 64‑bit targets.
#[derive(Debug, Copy, Clone, PartialEq, PartialOrd)]
#[repr(u8)]
pub(crate) enum Handle {
    Int(i64),
    Real(f64),
    Date(i64),
    Var(TinyArray),
    VarRef(Slice),
    Atom(TinyArray),
    AtomRef(Slice),
    Str(TinyArray),
    StrRef(Slice),
    Bin(TinyArray),
    BinRef(Slice),
    FuncRef(Slice),
    ListRef(Slice),
    ListCRef(Slice),
    TupleRef(Slice),
}

/// A compact, copyable handle referencing a term stored in a [`Arena`].
///
/// Internally a `Term` stores a single [`Handle`] enum variant.
/// On 64‑bit targets the discriminant and associated payload occupy
/// 16 bytes in total.  Users should never construct `Term` values
/// directly; instead use the associated constructors or the
/// convenience macros in the [`term`] module.
/// Instances of `Term` are cheap to copy (`Copy` and `Clone`).

// TODO: Consider implementing Hash, Eq, and Ord. Verify whether it is valid
//       to provide PartialEq, Eq, PartialOrd, Ord, and Hash when:
//       - Two different Term handles may point to the same term value, or
//       - Two identical Term handles obtained from different arenas may
//         represent distinct term values.
#[derive(Copy, Clone, PartialEq, PartialOrd)]
pub struct Term(pub(crate) Handle);

impl AsRef<Term> for Term {
    fn as_ref(&self) -> &Self {
        self
    }
}

macro_rules! impl_from_integers_for_term {
    ($($t:ty),* $(,)?) => {$(
        impl From<$t> for Term {
            #[inline]
            fn from(v: $t) -> Self { Term::int(v as i64) }
        }
    )*};
}
impl_from_integers_for_term!(i8, i16, i32, i64, u8, u16, u32);

macro_rules! impl_from_floats_for_term {
    ($($t:ty),* $(,)?) => {$(
        impl From<$t> for Term {
            #[inline]
            fn from(v: $t) -> Self { Term::real(v as f64) }
        }
    )*};
}
impl_from_floats_for_term!(f32, f64);

pub trait IntoTerm {
    fn into_term(self, arena: &mut Arena) -> Term;
}

macro_rules! impl_intoterm_for_integers {
    ($($t:ty),* $(,)?) => {$(
        impl IntoTerm for $t {
            #[inline]
            fn into_term(self, _arena: &mut Arena) -> Term { Term::int(self as i64) }
        }
    )*};
}
impl_intoterm_for_integers!(i8, i16, i32, i64, u8, u16, u32);

macro_rules! impl_intoterm_for_floats {
    ($($t:ty),* $(,)?) => {$(
        impl IntoTerm for $t {
            #[inline]
            fn into_term(self, _arena: &mut Arena) -> Term { Term::real(self as f64) }
        }
    )*};
}
impl_intoterm_for_floats!(f32, f64);

impl<'a> IntoTerm for &'a str {
    #[inline]
    fn into_term(self, arena: &mut Arena) -> Term {
        Term::str(arena, self)
    }
}

impl<'a> IntoTerm for &'a [u8] {
    #[inline]
    fn into_term(self, arena: &mut Arena) -> Term {
        Term::bin(arena, self)
    }
}

impl<'a> IntoTerm for Cow<'a, str> {
    #[inline]
    fn into_term(self, arena: &mut Arena) -> Term {
        match self {
            Cow::Borrowed(s) => Term::str(arena, s),
            Cow::Owned(s) => Term::str(arena, s),
        }
    }
}

impl<'a> IntoTerm for Cow<'a, [u8]> {
    #[inline]
    fn into_term(self, arena: &mut Arena) -> Term {
        match self {
            Cow::Borrowed(s) => Term::bin(arena, s),
            Cow::Owned(s) => Term::bin(arena, s),
        }
    }
}

impl IntoTerm for String {
    #[inline]
    fn into_term(self, arena: &mut Arena) -> Term {
        Term::str(arena, &self)
    }
}

impl IntoTerm for std::string::String {
    #[inline]
    fn into_term(self, arena: &mut Arena) -> Term {
        Term::str(arena, &self)
    }
}

impl IntoTerm for Vec<u8> {
    #[inline]
    fn into_term(self, arena: &mut Arena) -> Term {
        Term::bin(arena, &self)
    }
}

impl IntoTerm for Term {
    #[inline]
    fn into_term(self, _arena: &mut Arena) -> Term {
        self
    }
}

impl IntoTerm for &Term {
    #[inline]
    fn into_term(self, _arena: &mut Arena) -> Term {
        *self
    }
}

impl<F> IntoTerm for F
where
    F: FnOnce(&mut Arena) -> Term,
{
    #[inline]
    fn into_term(self, arena: &mut Arena) -> Term {
        self(arena)
    }
}

impl Term {
    /// Construct a new integer term.  The full 64 bit two's complement
    /// representation of `i` is stored in the payload.  No truncation
    /// occurs.
    #[inline]
    pub fn int(i: impl Into<i64>) -> Self {
        Self(Handle::Int(i.into()))
    }

    /// Construct a new floating point term.  The full 64 bit IEEE‑754
    /// bit pattern is stored in the payload without truncation.
    #[inline]
    pub fn real(f: impl Into<f64>) -> Self {
        Self(Handle::Real(f.into()))
    }

    /// Construct a new date term representing a Unix epoch in
    /// milliseconds.  Dates share the same underlying storage as
    /// integers but use a distinct tag so they do not compare equal
    /// with integer terms.
    #[inline]
    pub fn date(ms: impl Into<i64>) -> Self {
        Self(Handle::Date(ms.into()))
    }

    /// Construct or intern an atom into the arena and produce a term
    /// referencing it.  Small atom names (≤14 bytes of UTF‑8) are
    /// inlined directly into the handle; longer names are interned
    /// into the arena and referenced by index and length.
    #[inline]
    pub fn atom(arena: &mut Arena, name: impl AsRef<str>) -> Self {
        let name = name.as_ref();
        let bytes = name.as_bytes();
        if bytes.len() <= 14 {
            let mut buf = [0u8; 14];
            buf[..bytes.len()].copy_from_slice(bytes);
            Self(Handle::Atom(TinyArray {
                bytes: buf,
                len: bytes.len() as u8,
            }))
        } else {
            Self(Handle::AtomRef(arena.intern_str(name)))
        }
    }

    /// Construct or intern a variable into the arena and produce a
    /// term referencing it.  Small variable names (≤14 bytes) are
    /// inlined directly into the handle; longer names are interned in
    /// the arena and referenced by index.
    #[inline]
    pub fn var(arena: &mut Arena, name: impl AsRef<str>) -> Self {
        let name = name.as_ref();
        let bytes = name.as_bytes();
        if bytes.len() <= 14 {
            let mut buf = [0u8; 14];
            buf[..bytes.len()].copy_from_slice(bytes);
            Self(Handle::Var(TinyArray {
                bytes: buf,
                len: bytes.len() as u8,
            }))
        } else {
            Self(Handle::VarRef(arena.intern_str(name)))
        }
    }

    /// Construct or intern a UTF‑8 string into the arena and produce a
    /// term referencing it.  Strings longer than 14 bytes are interned
    /// in the arena; shorter strings are inlined.  Invalid UTF‑8 will
    /// result in an error.
    #[inline]
    pub fn str(arena: &mut Arena, s: impl AsRef<str>) -> Self {
        let s = s.as_ref();
        let bytes = s.as_bytes();
        if bytes.len() <= 14 {
            let mut buf = [0u8; 14];
            buf[..bytes.len()].copy_from_slice(bytes);
            Self(Handle::Str(TinyArray {
                bytes: buf,
                len: bytes.len() as u8,
            }))
        } else {
            Self(Handle::StrRef(arena.intern_str(s)))
        }
    }

    /// Construct or intern a binary blob into the arena and produce a
    /// term referencing it.  Blobs longer than 14 bytes are interned
    /// in the arena; shorter blobs are inlined.
    #[inline]
    pub fn bin(arena: &mut Arena, bytes: impl AsRef<[u8]>) -> Self {
        let bytes = bytes.as_ref();
        if bytes.len() <= 14 {
            let mut buf = [0u8; 14];
            buf[..bytes.len()].copy_from_slice(bytes);
            Self(Handle::Bin(TinyArray {
                bytes: buf,
                len: bytes.len() as u8,
            }))
        } else {
            Self(Handle::BinRef(arena.intern_bytes(bytes)))
        }
    }

    /// Construct a new compound term by interning the functor and
    /// arguments in the arena.  The returned term references a slice
    /// in the arena's term storage consisting of the functor atom as
    /// the first entry followed by the argument handles.  A functor of
    /// arity zero results in an atom.
    #[inline]
    pub fn func(
        arena: &mut Arena,
        functor: impl AsRef<str>,
        args: impl IntoIterator<Item = impl IntoTerm>,
    ) -> Self {
        let functor_atom = Self::atom(arena, functor);
        let mut args = args.into_iter();
        let Some(first) = args.next() else {
            return functor_atom;
        };
        Self(Handle::FuncRef(arena.intern_func(
            functor_atom,
            std::iter::once(first).chain(args),
        )))
    }

    /// Construct a new compound term by interning the functor and its arguments
    /// into the arena as a sequence of terms (functor first, then arguments).
    /// A functor with no arguments yields the atom itself.  Errors if
    /// no functor is provided or if the first term is not an atom.
    #[inline]
    pub fn funcv(
        arena: &mut Arena,
        terms: impl IntoIterator<Item = impl IntoTerm>,
    ) -> Result<Self, TermError> {
        let mut terms = terms.into_iter();
        let Some(functor_atom) = terms.next() else {
            return Err(TermError::MissingFunctor);
        };
        let functor_atom = functor_atom.into_term(arena);
        if !functor_atom.is_atom() {
            return Err(TermError::InvalidFunctor(functor_atom));
        }
        let Some(first) = terms.next() else {
            return Ok(functor_atom);
        };
        Ok(Self(Handle::FuncRef(arena.intern_func(
            functor_atom,
            std::iter::once(first).chain(terms),
        ))))
    }

    /// Constructs a new list. A list is represented internally as an
    /// array of terms. If `terms` is empty, returns `nil`.
    #[inline]
    pub fn list(arena: &mut Arena, terms: impl IntoIterator<Item = impl IntoTerm>) -> Self {
        let mut terms = terms.into_iter();
        let Some(first) = terms.next() else {
            return Self::NIL;
        };
        Self(Handle::ListRef(
            arena.intern_seq(std::iter::once(first).chain(terms)),
        ))
    }

    /// Constructs a new improper list. An improper list is represented as
    /// a list and additional argument. If `terms` is empty, returns `nil`.
    #[inline]
    pub fn listc(
        arena: &mut Arena,
        terms: impl IntoIterator<Item = impl IntoTerm>,
        tail: impl IntoTerm,
    ) -> Self {
        let mut terms = terms.into_iter();
        let Some(first) = terms.next() else {
            return Self::NIL;
        };
        let tail = tail.into_term(arena);
        if tail != Term::NIL {
            Self(Handle::ListCRef(arena.intern_seq_plus_one(
                std::iter::once(first).chain(terms),
                tail,
            )))
        } else {
            Self(Handle::ListRef(
                arena.intern_seq(std::iter::once(first).chain(terms)),
            ))
        }
    }

    /// Constructs a new tuple. A tuple is represented internally as an array
    /// of terms.
    #[inline]
    pub fn tuple(arena: &mut Arena, terms: impl IntoIterator<Item = impl IntoTerm>) -> Self {
        let mut terms = terms.into_iter();
        let Some(first) = terms.next() else {
            return Self::UNIT;
        };
        Self(Handle::TupleRef(
            arena.intern_seq(std::iter::once(first).chain(terms)),
        ))
    }

    /// Constant representing the zero‑arity tuple (unit).  Internally
    /// this is the atom `"unit"` encoded as a small atom.  It may
    /// be copied freely and does not depend on any arena.
    pub const UNIT: Self = {
        let buf: [u8; 14] = [b'u', b'n', b'i', b't', 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
        Self(Handle::Atom(TinyArray { bytes: buf, len: 4 }))
    };

    /// Constant representing the empty list (nil).  Internally this is
    /// the atom `"nil"` encoded as a small atom.  It may be copied
    /// freely and does not depend on any arena.
    pub const NIL: Self = {
        let buf: [u8; 14] = [b'n', b'i', b'l', 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
        Self(Handle::Atom(TinyArray { bytes: buf, len: 3 }))
    };

    /// Returns the value if `term` is an integer, otherwise an error.
    #[inline]
    pub fn unpack_int(&self, arena: &Arena) -> Result<i64, TermError> {
        arena.unpack_int(self)
    }

    /// Returns the value if `term` is a real, otherwise an error.
    #[inline]
    pub fn unpack_real(&self, arena: &Arena) -> Result<f64, TermError> {
        arena.unpack_real(self)
    }

    /// Returns the value if `term` is a date, otherwise an error.
    #[inline]
    pub fn unpack_date(&self, arena: &Arena) -> Result<i64, TermError> {
        arena.unpack_date(self)
    }

    /// Returns the string slice if `term` is a string, otherwise an error.
    #[inline]
    pub fn unpack_str<'a>(&'a self, arena: &'a Arena) -> Result<&'a str, TermError> {
        arena.unpack_str(self)
    }

    /// Returns the slice if `term` is a binary blob, otherwise an error.
    #[inline]
    pub fn unpack_bin<'a>(&'a self, arena: &'a Arena) -> Result<&'a [u8], TermError> {
        arena.unpack_bin(self)
    }

    /// Returns the name if `term` is an atom, otherwise an error.
    #[inline]
    pub fn unpack_atom<'a>(
        &'a self,
        arena: &'a Arena,
        allowed_names: &[&str],
    ) -> Result<&'a str, TermError> {
        arena.unpack_atom(self, allowed_names)
    }

    /// Returns the name if `term` is a variable, otherwise an error.
    #[inline]
    pub fn unpack_var<'a>(
        &'a self,
        arena: &'a Arena,
        allowed_names: &[&str],
    ) -> Result<&'a str, TermError> {
        arena.unpack_var(self, allowed_names)
    }

    /// Returns the name and arguments if `term` is a compound term of any arity
    /// or an atom and its name is in `allowed_names` (or if `allowed_names` is empty),
    /// otherwise returns an error.
    #[inline]
    pub fn unpack_func_any<'a>(
        &'a self,
        arena: &'a Arena,
        allowed_names: &[&str],
    ) -> Result<(&'a Term, &'a [Term]), TermError> {
        arena.unpack_func_any(self, allowed_names)
    }

    /// Returns the name and arguments if `term` is a compound term of arity `ARITY`
    /// (or an atom if `ARITY == 0`) and its name is in `allowed_names` (or if `allowed_names` is empty),
    /// otherwise returns an error.
    #[inline]
    pub fn unpack_func<'a, const ARITY: usize>(
        &'a self,
        arena: &'a Arena,
        allowed_names: &[&str],
    ) -> Result<(&'a Term, [Term; ARITY]), TermError> {
        arena.unpack_func(self, allowed_names)
    }

    /// Returns the slice with list elements and the tail if `term` is a list,
    /// otherwise returns an error.
    #[inline]
    pub fn unpack_list<'a>(
        &'a self,
        arena: &'a Arena,
    ) -> Result<(&'a [Term], &'a Term), TermError> {
        arena.unpack_list(self)
    }

    /// Returns the slice with tuple elements if `term` is a tuple of any arity,
    /// otherwise returns an error.
    #[inline]
    pub fn unpack_tuple_any<'a>(&'a self, arena: &'a Arena) -> Result<&'a [Term], TermError> {
        arena.unpack_tuple_any(self)
    }

    /// Returns the tuple elements if `term` is a tuple of arity `ARITY`,
    /// otherwise returns an error.
    #[inline]
    pub fn unpack_tuple<const ARITY: usize>(
        &self,
        arena: &Arena,
    ) -> Result<[Term; ARITY], TermError> {
        arena.unpack_tuple(self)
    }

    /// Returns `true` if the value fits directly in `Term` without arena storage,
    /// i.e. `int`, `real`, `date`, or a small `atom`, `var`, `str`, or `bin`.
    #[inline]
    pub fn is_inline(&self) -> bool {
        match &self.0 {
            Handle::Int(_)
            | Handle::Real(_)
            | Handle::Date(_)
            | Handle::Atom(_)
            | Handle::Var(_)
            | Handle::Str(_)
            | Handle::Bin(_) => true,
            Handle::AtomRef(_)
            | Handle::VarRef(_)
            | Handle::StrRef(_)
            | Handle::BinRef(_)
            | Handle::FuncRef(_)
            | Handle::ListRef(_)
            | Handle::ListCRef(_)
            | Handle::TupleRef(_) => false,
        }
    }

    /// Returns `true` if the term is a compound term.
    #[inline]
    pub fn is_func(&self) -> bool {
        matches!(self.0, Handle::FuncRef(_))
    }

    /// Returns `true` if the term is a list.
    #[inline]
    pub fn is_list(&self) -> bool {
        matches!(self.0, Handle::ListRef(_) | Handle::ListCRef(_)) || *self == Self::NIL
    }

    /// Returns `true` if the term is a tuple.
    #[inline]
    pub fn is_tuple(&self) -> bool {
        matches!(self.0, Handle::TupleRef(_)) || *self == Self::UNIT
    }

    /// Returns `true` if the term is an integer.
    #[inline]
    pub fn is_int(&self) -> bool {
        matches!(self.0, Handle::Int(_))
    }

    /// Returns `true` if the term is a real (floating-point) number.
    #[inline]
    pub fn is_real(&self) -> bool {
        matches!(self.0, Handle::Real(_))
    }

    /// Returns `true` if the term is a date.
    #[inline]
    pub fn is_date(&self) -> bool {
        matches!(self.0, Handle::Date(_))
    }

    /// Returns `true` if the term is an atom.
    #[inline]
    pub fn is_atom(&self) -> bool {
        matches!(self.0, Handle::Atom(_) | Handle::AtomRef(_))
    }

    /// Returns `true` if the term is a variable.
    #[inline]
    pub fn is_var(&self) -> bool {
        matches!(self.0, Handle::Var(_) | Handle::VarRef(_))
    }

    /// Returns `true` if the term is a number (`int`, `real`, or `date`).
    #[inline]
    pub fn is_number(&self) -> bool {
        matches!(self.0, Handle::Int(_) | Handle::Real(_) | Handle::Date(_))
    }

    /// Returns `true` if the term is a string.
    #[inline]
    pub fn is_str(&self) -> bool {
        matches!(self.0, Handle::Str(_) | Handle::StrRef(_))
    }

    /// Returns `true` if the term is a binary blob.
    #[inline]
    pub fn is_bin(&self) -> bool {
        matches!(self.0, Handle::Bin(_) | Handle::BinRef(_))
    }

    /// Returns the arity of the term. Currently the arity of lists and variables is 0.
    #[inline]
    pub fn arity(&self) -> usize {
        match &self.0 {
            Handle::Atom(_)
            | Handle::AtomRef(_)
            | Handle::Int(_)
            | Handle::Real(_)
            | Handle::Date(_)
            | Handle::Str(_)
            | Handle::StrRef(_)
            | Handle::Bin(_)
            | Handle::BinRef(_) => 0,
            Handle::FuncRef(Slice { len: n, .. }) => (n - 1) as usize,
            Handle::TupleRef(Slice { len: n, .. }) => *n as usize,
            Handle::ListRef(_) | Handle::ListCRef(_) | Handle::Var(_) | Handle::VarRef(_) => 0,
        }
    }

    /// Returns the name of a compound term, atom, or variable.
    /// Use [`atom_name`], [`func_name`], or [`var_name`]
    /// to ensure the term is of a specific kind.
    #[inline]
    pub fn name<'a>(&'a self, arena: &'a Arena) -> Result<&'a str, TermError> {
        arena.name(self)
    }

    /// Returns the name of an atom,
    #[inline]
    pub fn atom_name<'a>(&'a self, arena: &'a Arena) -> Result<&'a str, TermError> {
        arena.unpack_atom(self, &[])
    }

    /// Returns the name of a variable.
    #[inline]
    pub fn var_name<'a>(&'a self, arena: &'a Arena) -> Result<&'a str, TermError> {
        arena.unpack_var(self, &[])
    }

    /// Returns the name of a compund term.
    #[inline]
    pub fn func_name<'a>(&'a self, arena: &'a Arena) -> Result<&'a str, TermError> {
        let (functor, _) = arena.unpack_func_any(self, &[])?;
        arena.atom_name(functor)
    }

    /// Returns a string describing the kind of this term.
    #[inline]
    pub fn kind_name(&self) -> &'static str {
        match &self.0 {
            Handle::Int(_) => "int",
            Handle::Real(_) => "real",
            Handle::Date(_) => "date",
            Handle::Var(_) | Handle::VarRef(_) => "var",
            Handle::Atom(_) | Handle::AtomRef(_) => "atom",
            Handle::Str(_) | Handle::StrRef(_) => "str",
            Handle::Bin(_) | Handle::BinRef(_) => "bin",
            Handle::FuncRef(_) => "func",
            Handle::ListRef(_) | Handle::ListCRef(_) => "list",
            Handle::TupleRef(_) => "tuple",
        }
    }
}

/// Implements the standard [`Debug`] formatter for [`Term`].
///
/// This prints a developer-friendly representation of the term,
/// showing its kind (e.g. `int`, `atom`, `list`, `tuple`) and
/// its internal value in a form useful for debugging.  
///
/// The output is not guaranteed to be stable across versions and
/// should not be parsed; it is intended purely for diagnostics
/// and logging.
///
/// # Example
/// ```rust
/// # use arena_terms::Term;
/// let t = Term::int(42);
/// println!("{:?}", t); // e.g. prints `Int(42)`
/// ```
impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            Handle::Int(i) => f.debug_tuple("Int").field(i).finish(),
            Handle::Real(r) => f.debug_tuple("Real").field(r).finish(),
            Handle::Date(d) => f.debug_tuple("Date").field(d).finish(),
            Handle::Var(v) => {
                let name =
                    core::str::from_utf8(&v.bytes[..v.len as usize]).unwrap_or("<invalid utf8>");
                f.debug_struct("Var").field("name", &name).finish()
            }
            Handle::VarRef(v) => f
                .debug_struct("VarRef")
                .field("epoch_id", &v.epoch_id)
                .field("index", &v.index)
                .field("len", &v.len)
                .finish(),
            Handle::Atom(a) => {
                let name =
                    core::str::from_utf8(&a.bytes[..a.len as usize]).unwrap_or("<invalid utf8>");
                f.debug_struct("Atom").field("name", &name).finish()
            }
            Handle::AtomRef(v) => f
                .debug_struct("AtomRef")
                .field("epoch_id", &v.epoch_id)
                .field("index", &v.index)
                .field("len", &v.len)
                .finish(),
            Handle::Str(s) => {
                let value =
                    core::str::from_utf8(&s.bytes[..s.len as usize]).unwrap_or("<invalid utf8>");
                f.debug_struct("Str").field("value", &value).finish()
            }
            Handle::StrRef(v) => f
                .debug_struct("StrRef")
                .field("epoch_id", &v.epoch_id)
                .field("index", &v.index)
                .field("len", &v.len)
                .finish(),
            Handle::Bin(b) => {
                let slice = &b.bytes[..b.len as usize];
                f.debug_struct("Bin").field("bytes", &slice).finish()
            }
            Handle::BinRef(v) => f
                .debug_struct("BinRef")
                .field("epoch_id", &v.epoch_id)
                .field("index", &v.index)
                .field("len", &v.len)
                .finish(),
            Handle::FuncRef(v) => f
                .debug_struct("Func")
                .field("epoch_id", &v.epoch_id)
                .field("index", &v.index)
                .field("len", &v.len)
                .finish(),
            Handle::ListRef(v) => f
                .debug_struct("List")
                .field("epoch_id", &v.epoch_id)
                .field("index", &v.index)
                .field("len", &v.len)
                .finish(),
            Handle::ListCRef(v) => f
                .debug_struct("ListC")
                .field("epoch_id", &v.epoch_id)
                .field("index", &v.index)
                .field("len", &v.len)
                .finish(),
            Handle::TupleRef(v) => f
                .debug_struct("Tuple")
                .field("epoch_id", &v.epoch_id)
                .field("index", &v.index)
                .field("len", &v.len)
                .finish(),
        }
    }
}

/// Convenience macros to construct func, list and tuple.
#[macro_export]
macro_rules! list {
    // with tail, explicit arena
    ($($arg:expr),* $(,)?; $tail:expr => $arena:expr) => {
        $crate::list!($($arg),* ; $tail)($arena)
    };
    // without tail, explicit arena
    ($($arg:expr),* $(,)? => $arena:expr) => {
        $crate::list!($($arg),*)($arena)
    };
    // with tail, implicit arena
    ($($arg:expr),* $(,)?; $tail:expr) => { (|__arena: &mut $crate::Arena| {
        let __args: &[$crate::Term] = &[$($arg.into_term(__arena)),*];
        let __tail: Term = $tail.into_term(__arena);
        __arena.listc(__args, __tail)
    })};
    // without tail, implicit arena
    ($($arg:expr),* $(,)?) => { (|__arena: &mut $crate::Arena| {
        let __args: &[$crate::Term] = &[$($arg.into_term(__arena)),*];
        __arena.list(__args)
    })};
}

#[macro_export]
macro_rules! tuple {
    // explicit arena
    ($($arg:expr),* $(,)? => $arena:expr) => {
        $crate::tuple!($($arg),*)($arena)
    };
    // implicit arena
    ($($arg:expr),* $(,)?) => { (|__arena: &mut $crate::Arena| {
        let __args: &[$crate::Term] = &[$($arg.into_term(__arena)),*];
        __arena.tuple(__args)
    })};
}

#[macro_export]
macro_rules! func {
    // explicit arena
    ($functor:expr; $($arg:expr),+ $(,)? => $arena:expr) => {
        $crate::func!($functor; $($arg),+)($arena)
    };
    // implicit arena
    ($functor:expr; $($arg:expr),+ $(,)?) => { (|__arena: &mut $crate::Arena| {
        let __args: &[$crate::Term] = &[$($arg.into_term(__arena)),+];
        __arena.func($functor, __args)
    })};
}

#[macro_export]
macro_rules! atom {
    // explicit arena
    ($functor:expr => $arena:expr) => {
        $crate::atom!($functor)($arena)
    };
    // implicit arena
    ($functor:expr) => {
        (|__arena: &mut $crate::Arena| __arena.atom($functor))
    };
}

#[macro_export]
macro_rules! var {
    // explicit arena
    ($name:expr => $arena:expr) => {
        $crate::var!($name)($arena)
    };
    // implicit arena
    ($name:expr) => {
        (|__arena: &mut $crate::Arena| __arena.var($name))
    };
}

#[macro_export]
macro_rules! date {
    ($value:expr) => {
        $crate::Term::date($value)
    };
}

#[macro_export]
macro_rules! unit {
    () => {
        $crate::Term::UNIT
    };
}

#[macro_export]
macro_rules! nil {
    () => {
        $crate::Term::NIL
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::View;
    use std::fmt::Write;

    #[test]
    fn term_size_is_16_bytes() {
        assert_eq!(core::mem::size_of::<Term>(), 16);
    }

    #[test]
    fn option_term_size_is_16_bytes() {
        assert_eq!(core::mem::size_of::<Option<Term>>(), 16);
    }

    #[test]
    fn small_atom_interning() {
        let mut arena = Arena::new();
        let a1 = Term::atom(&mut arena, "foo");
        let a2 = Term::atom(&mut arena, "foo");
        assert_eq!(a1, a2);
        if let Ok(View::Atom(name)) = a1.view(&arena) {
            assert_eq!(name, "foo");
        } else {
            panic!("wrong view");
        }
    }

    #[test]
    fn compound_construction_and_formatting() {
        let mut arena = Arena::new();
        let a = Term::int(1);
        let b = Term::real(2.0);
        let c = Term::date(1000);
        let d = Term::atom(&mut arena, "hello");
        let e = Term::var(&mut arena, "Hello");
        let f = Term::str(&mut arena, "A str\ning. Longer string.");
        let g = list![d, e, f => &mut arena];
        let h = tuple!(f, f => &mut arena);
        let p = Term::func(&mut arena, "point", &[a, b, c, d, e, f, g, h]);
        let p = func![
            "foo";
            Term::NIL,
            Term::UNIT,
            p,
            p,
            list![],
            list![a, b; c],
            => &mut arena
        ];
        dbg!(&p);
        dbg!(p.view(&arena).unwrap());
        dbg!(arena.stats());
        assert!(p.is_func());
        if let Ok(View::Func(_, functor, args)) = p.view(&arena) {
            assert_eq!(functor.atom_name(&arena).unwrap(), "foo");
            assert_eq!(p.arity(), 6);
            assert_eq!(args.len(), 6);
        } else {
            panic!("unexpected view");
        }

        let s = format!("{}", p.display(&arena));
        assert_eq!(
            s,
            "foo(nil, unit, point(1, 2.0, date{1970-01-01T00:00:01+00:00}, hello, Hello, \"A str\\ning. Longer string.\", [hello, Hello, \"A str\\ning. Longer string.\"], (\"A str\\ning. Longer string.\", \"A str\\ning. Longer string.\")), point(1, 2.0, date{1970-01-01T00:00:01+00:00}, hello, Hello, \"A str\\ning. Longer string.\", [hello, Hello, \"A str\\ning. Longer string.\"], (\"A str\\ning. Longer string.\", \"A str\\ning. Longer string.\")), nil, [1, 2.0 | date{1970-01-01T00:00:01+00:00}])"
        );
    }

    #[test]
    fn view_construction() {
        let mut a1 = Arena::new();
        let x = a1.atom("Hello, hello, quite long long string, world! X");
        dbg!(a1.view(&x).unwrap());
        dbg!(a1.stats());
        let p = list![x, x => &mut a1];
        dbg!(p);
        let v = a1.view(&p).unwrap();
        dbg!(v);
    }

    #[test]
    #[should_panic]
    fn arena_mismatch() {
        let a1 = Arena::new();
        let mut a2 = Arena::new();
        let y = a2.str("Hello, hello, quite long long string, world! Y");
        dbg!(a1.view(&y).unwrap());
    }

    #[test]
    #[should_panic]
    fn stale_term_str() {
        let mut a = Arena::new();
        let x = a.str("Hello, hello, quite long long string, world! Y");
        dbg!(&a);
        a.truncate(a.current_epoch()).unwrap();
        dbg!(a.view(&x).unwrap());
    }

    #[test]
    #[should_panic]
    fn stale_term_list() {
        let mut a = Arena::new();
        let _x = list![1, 2, 3 => &mut a];
        let epoch = a.begin_epoch().unwrap();
        dbg!(&epoch);
        let y = list![4, 5, 6 => &mut a];
        dbg!(&a);
        a.truncate(epoch).unwrap();
        dbg!(&a);
        dbg!(a.view(&y).unwrap());
    }

    #[test]
    fn big_term() {
        let mut a1 = Arena::new();
        let x = a1.atom("Hello, hello, quite long long string, world! X");
        let p = a1.func("foo", vec![x; 1_000_000]);
        assert!(p.arity() == 1_000_000);
        dbg!(a1.stats());
    }

    #[test]
    fn interface() {
        let a = &mut Arena::new();
        let s = String::from("x");
        let x1 = a.func(&s, &vec![Term::date(1000)]);
        let x2 = a.func(s.as_str(), vec![Term::date(1000)]);
        let x3 = a.func(s, &[Term::date(1000)]);
        let _x4 = a.func("x", [Term::date(1000)]);
        let _x5 = a.func("x", [x1, x2, x3]);
        let _x6 = a.func("x", (5..=6).map(|x| x as f64));
        let _x7 = a.func("x", vec![&x1, &x2, &x3]);
        let _x8 = a.func("x", &[x1, x2, x3]);
        let x9 = func!(
            String::from("aaa");
            x1, 1u8, 1i8, 2.0,
            "x",
            "X",
            atom!("ATOM"),
            var!("var"),
            "a string",
            b"a binary",
            1,
            2,
            3,
            4,
            6,
            unit!(),
            list![1, 2, 3; tuple!()],
            list![1, 2, 3; nil!()],
            => a
        );
        dbg!(a.view(&x9).unwrap());
        dbg!(a.stats());
    }

    #[test]
    fn into_test() {
        let mut arena = Arena::new();
        // You can mix numbers and strings; IntoTerm will pick the right constructor.
        let t1 = arena.term(1);
        let t2 = arena.term(2.0);
        let t3 = arena.term("x");
        let t4 = arena.term(b"bin" as &[u8]);
        let point1 = arena.func("point", [t1, t2, t3, t4]);
        // Equivalent to:
        let t1 = Term::int(1);
        let t2 = Term::real(2.0);
        let t3 = Term::str(&mut arena, "x");
        let t4 = Term::bin(&mut arena, b"bin");
        let point2 = arena.func("point", [t1, t2, t3, t4]);
        assert_eq!(arena.view(&point1).unwrap(), arena.view(&point2).unwrap());
        dbg!(arena.view(&point1).unwrap());

        // You can also provide closures returning Term.
        let lazy = Term::func(&mut arena, "lazy", [|arena: &mut Arena| arena.atom("ok")]);
        dbg!(arena.view(&lazy).unwrap());

        let list = arena.list([1, 2, 3]);
        dbg!(arena.view(&list).unwrap());
    }

    #[test]
    fn arena_truncate_test() {
        let a = &mut Arena::new();

        let t1 = a.str("a".repeat(1000));
        let _t5 = atom!("x".repeat(100) => a);
        let _t6 = var!("X".repeat(200) => a);
        let _t7 = a.bin(b"x".repeat(5000));
        let epoch1 = a.begin_epoch().unwrap();
        dbg!(a.stats());
        dbg!(&epoch1);
        let t2 = a.str("b".repeat(2000));
        let t3 = a.bin(b"b".repeat(3000));
        let _t4 = list![t1, t2, t3];
        let _t5 = atom!("z".repeat(4000) => a);
        let _t8 = var!("Z".repeat(2000) => a);
        let _t7 = a.bin(b"z".repeat(10_000));
        let epoch2 = a.begin_epoch().unwrap();
        dbg!(a.stats());
        dbg!(&epoch2);
        a.truncate(epoch2).unwrap();
        dbg!(a.stats());
    }

    #[test]
    fn funcv() {
        let a = &mut Arena::new();
        let xs = [a.atom("foo"), a.atom("x"), a.atom("y")];
        let x = a.funcv(xs).unwrap();
        let ys = [a.atom("x"), a.atom("y")];
        let y = a.func("foo", ys);
        assert_eq!(x.arity(), y.arity());
        if let Ok(View::Func(_, functor, args)) = x.view(&a) {
            assert_eq!(functor.name(a).unwrap(), "foo");
            assert_eq!(args.len(), 2);
        }
        if let Ok(View::Func(_, functor, args)) = y.view(&a) {
            assert_eq!(functor.name(a).unwrap(), "foo");
            assert_eq!(args.len(), 2);
        }
    }

    #[test]
    fn unpack() {
        let a = &mut Arena::new();
        let xs = [a.atom("foo"), a.atom("x"), a.atom("y")];
        let x = a.funcv(xs).unwrap();

        let (foo, [x, y]) = x.unpack_func(a, &["foo", "boo"]).unwrap();
        dbg!((foo, x, y));

        let z = tuple!(1 => a);
        assert_eq!(z.arity(), 1);
    }

    #[test]
    fn arity_primitives_and_lists_are_zero() {
        let a = &mut Arena::new();

        let t_int = Term::int(42);
        let t_real = Term::real(3.14);
        let t_atom = Term::atom(a, "ok");
        let t_var = Term::var(a, "X");
        let t_str = Term::str(a, "hello");
        let t_bin = Term::bin(a, &[1, 2, 3, 4]);
        let t_list = Term::list(a, &[Term::int(1), Term::int(2), Term::int(3)]);

        assert_eq!(t_int.arity(), 0);
        assert_eq!(t_real.arity(), 0);
        assert_eq!(t_atom.arity(), 0);
        assert_eq!(t_var.arity(), 0);
        assert_eq!(t_str.arity(), 0);
        assert_eq!(t_bin.arity(), 0);
        assert_eq!(t_list.arity(), 0); // lists are 0 by current implementation
    }

    #[test]
    fn arity_for_tuples_and_funcs() {
        let a = &mut Arena::new();

        let t2 = Term::tuple(a, &[Term::int(1), Term::int(2)]);
        let t3 = Term::tuple(a, &[Term::int(1), Term::int(2), Term::int(3)]);
        assert_eq!(t2.arity(), 2);
        assert_eq!(t3.arity(), 3);

        let f0 = Term::func(a, "nilary", &[] as &[Term]); // creates an atom `nilary`
        let f2 = Term::func(a, "pair", &[Term::int(1), Term::int(2)]);
        let f3 = Term::func(a, "triple", &[Term::int(1), Term::int(2), Term::int(3)]);

        assert_eq!(f0.arity(), 0);
        assert_eq!(f2.arity(), 2);
        assert_eq!(f3.arity(), 3);
    }

    #[test]
    fn name_and_kind_name() {
        let a = &mut Arena::new();

        let atom = Term::atom(a, "foo");
        let var = Term::var(a, "X");
        let fun = Term::func(a, "bar", &[Term::int(1)]);
        let tup = Term::tuple(a, &[Term::int(1), Term::int(2)]);
        let lst = Term::list(a, &[Term::int(1), Term::int(2), Term::int(3)]);

        // `name()` should resolve atom/var names and compound heads.
        assert_eq!(atom.name(&a).unwrap(), "foo");
        assert_eq!(var.name(&a).unwrap(), "X");
        assert_eq!(fun.name(&a).unwrap(), "bar");

        // `kind_name()` should report stable kind strings
        assert_eq!(atom.kind_name(), "atom");
        assert_eq!(var.kind_name(), "var");
        assert_eq!(fun.kind_name(), "func");
        assert_eq!(tup.kind_name(), "tuple");
        assert_eq!(lst.kind_name(), "list");
        assert_eq!(Term::int(7).kind_name(), "int");
        assert_eq!(Term::str(a, "s").kind_name(), "str");
    }

    #[test]
    fn is_func_tuple_list() {
        let a = &mut Arena::new();

        let f2 = Term::func(a, "pair", &[Term::int(1), Term::int(2)]);
        let tup = Term::tuple(a, &[Term::int(1), Term::int(2)]);
        let lst = Term::list(a, &[Term::int(1), Term::int(2), Term::int(3)]);

        assert!(f2.is_func());
        assert!(tup.is_tuple());
        assert!(lst.is_list());

        assert!(!f2.is_tuple());
        assert!(!f2.is_list());
        assert!(!tup.is_func());
        assert!(!lst.is_func());
        assert!(!lst.is_tuple());
    }

    #[test]
    fn is_inline_obvious_cases() {
        let a = &mut Arena::new();

        let i = Term::int(42);
        let f0 = Term::func(a, "nilary", &[] as &[Term]);
        let tup = Term::tuple(a, &[Term::int(1), Term::int(2)]);
        let lst = Term::list(a, &[Term::int(1), Term::int(2)]);

        // Obvious truthy/falsey cases that don't depend on small/large thresholds.
        assert!(i.is_inline());
        assert!(f0.is_inline()); // f0 is an atom
        assert!(!tup.is_inline());
        assert!(!lst.is_inline());
    }

    #[test]
    fn is_atom_var_str_bin_number_minimal() {
        let a = &mut Arena::new();

        let at = Term::atom(a, "foo");
        let vr = Term::var(a, "X");
        let st = Term::str(a, "hi");
        let bi = Term::bin(a, &[1, 2, 3, 4]);
        let i = Term::int(7);

        assert!(at.is_atom());
        assert!(vr.is_var());
        assert!(st.is_str());
        assert!(bi.is_bin());

        assert!(!at.is_var());
        assert!(!vr.is_atom());
        assert!(!st.is_bin());
        assert!(!bi.is_str());

        // is_number is true for ints (and, by spec, also for real/date—tested here with int).
        assert!(i.is_number());
        assert!(!at.is_number());
        assert!(!st.is_number());
        assert!(!bi.is_number());
    }

    #[test]
    fn nil_and_tuple_edge_behavior() {
        let a = &mut Arena::new();

        // NIL should count as a list per your is_list() (*self == Self::NIL)
        assert!(Term::NIL.is_list());
        assert!(!Term::NIL.is_tuple());
        assert!(!Term::NIL.is_func());
        assert_eq!(Term::NIL.arity(), 0);

        // Regular tuple is a tuple; arity equals length.
        let t = Term::tuple(a, &[Term::int(1), Term::int(2), Term::int(3)]);
        assert!(t.is_tuple());
        assert_eq!(t.arity(), 3);
        assert!(!t.is_list());
        assert!(!t.is_func());
    }

    #[test]
    fn arity_consistency_with_predicates() {
        let a = &mut Arena::new();

        let f3 = Term::func(a, "triple", &[Term::int(1), Term::int(2), Term::int(3)]);
        let t2 = Term::tuple(a, &[Term::int(1), Term::int(2)]);
        let l2 = Term::list(a, &[Term::int(1), Term::int(2)]);
        let v = Term::var(a, "X");

        assert!(f3.is_func());
        assert_eq!(f3.arity(), 3);

        assert!(t2.is_tuple());
        assert_eq!(t2.arity(), 2);

        assert!(l2.is_list());
        assert_eq!(l2.arity(), 0); // lists are defined as 0-arity

        assert!(v.is_var());
        assert_eq!(v.arity(), 0); // variables are 0-arity
    }

    #[test]
    fn name_and_kind_name_roundtrip() {
        let a = &mut Arena::new();

        let atom = Term::atom(a, "foo");
        let var = Term::var(a, "X");
        let fun = Term::func(a, "bar", &[Term::int(1)]);
        let tup = Term::tuple(a, &[Term::int(1), Term::int(2)]);
        let lst = Term::list(a, &[Term::int(1), Term::int(2), Term::int(3)]);

        // name(): atoms, variables, and compound heads resolve
        assert_eq!(atom.name(&a).unwrap(), "foo");
        assert_eq!(var.name(&a).unwrap(), "X");
        assert_eq!(fun.name(&a).unwrap(), "bar");

        // kind_name(): stable kind labels
        assert_eq!(atom.kind_name(), "atom");
        assert_eq!(var.kind_name(), "var");
        assert_eq!(fun.kind_name(), "func");
        assert_eq!(tup.kind_name(), "tuple");
        assert_eq!(lst.kind_name(), "list");
        assert_eq!(Term::int(7).kind_name(), "int");
        assert_eq!(Term::str(a, "s").kind_name(), "str");
    }

    #[test]
    fn unpack_primitives_ok() {
        let a = &mut Arena::new();

        let t_int = Term::int(42);
        let t_real = Term::real(3.5);
        let t_date = Term::date(2);
        let t_str = Term::str(a, "hello");
        let t_bin = Term::bin(a, &[1u8, 2, 3, 4]);

        assert_eq!(t_int.unpack_int(a).unwrap(), 42);
        assert!((t_real.unpack_real(a).unwrap() - 3.5).abs() < f64::EPSILON);
        assert_eq!(t_date.unpack_date(a).unwrap(), 2);

        assert_eq!(t_str.unpack_str(a).unwrap(), "hello");
        assert_eq!(t_bin.unpack_bin(a).unwrap(), &[1, 2, 3, 4]);
    }

    #[test]
    fn unpack_primitives_wrong_type_errs() {
        let a = &mut Arena::new();

        let not_int = Term::str(a, "nope");
        let not_real = Term::int(1);
        let not_date = Term::str(a, "2024-01-02");

        assert!(not_int.unpack_int(a).is_err());
        assert!(not_real.unpack_real(a).is_err());
        assert!(not_date.unpack_date(a).is_err());

        let not_str = Term::int(5);
        let not_bin = Term::str(a, "bytes");
        assert!(not_str.unpack_str(a).is_err());
        assert!(not_bin.unpack_bin(a).is_err());
    }

    #[test]
    fn unpack_atom_and_var_with_allowed_names() {
        let a = &mut Arena::new();

        let at_ok = Term::atom(a, "foo");
        let at_no = Term::atom(a, "bar");
        let vr_ok = Term::var(a, "X");
        let vr_no = Term::var(a, "Y");

        // Allowed lists
        let allowed_atoms = ["foo", "baz"];
        let allowed_vars = ["X", "Z"];

        assert_eq!(at_ok.unpack_atom(a, &allowed_atoms).unwrap(), "foo");
        assert!(at_no.unpack_atom(a, &allowed_atoms).is_err());

        assert_eq!(vr_ok.unpack_var(a, &allowed_vars).unwrap(), "X");
        assert!(vr_no.unpack_var(a, &allowed_vars).is_err());

        // Empty allowed_names means "any"
        assert_eq!(at_no.name(a).unwrap(), "bar");
        assert_eq!(vr_no.var_name(a).unwrap(), "Y");
    }

    #[test]
    fn unpack_func_any_and_arity_specific() {
        let a = &mut Arena::new();

        let f0 = Term::func(a, "nilary", &[] as &[Term]);
        let f2 = Term::func(a, "pair", &[Term::int(1), Term::int(2)]);
        let f3 = Term::func(a, "triple", &[Term::int(1), Term::int(2), Term::int(3)]);

        // Any arity, name filtering
        {
            let (name, args) = f2.unpack_func_any(a, &["pair", "other"]).unwrap();
            assert_eq!(name.name(a).unwrap(), "pair");
            assert_eq!(args.len(), 2);
            assert_eq!(args[0].unpack_int(a).unwrap(), 1);
            assert_eq!(args[1].unpack_int(a).unwrap(), 2);

            // empty allowed_names accepts anything
            let (name0, args0) = f0.unpack_func_any(a, &[]).unwrap();
            assert_eq!(name0.name(a).unwrap(), "nilary");
            assert!(args0.is_empty());

            // disallowed name should error
            assert!(f3.unpack_func_any(a, &["not_triple"]).is_err());
        }

        // Fixed arity (const generic)
        {
            let (name2, [x, y]) = f2.unpack_func(a, &["pair"]).unwrap();
            assert_eq!(name2.name(a).unwrap(), "pair");
            assert_eq!(x.unpack_int(a).unwrap(), 1);
            assert_eq!(y.unpack_int(a).unwrap(), 2);

            // Arity mismatch should error
            assert!(f3.unpack_func::<2>(a, &["triple"]).is_err());

            // Name not allowed should error
            assert!(f2.unpack_func::<2>(a, &["other"]).is_err());
        }
    }

    #[test]
    fn unpack_list_proper_and_tail() {
        let a = &mut Arena::new();

        let l0 = Term::list(a, &[] as &[Term]);
        let (elems0, tail0) = l0.unpack_list(a).unwrap();
        assert!(elems0.is_empty());
        assert_eq!(*tail0, Term::NIL);

        let l3 = Term::list(a, &[Term::int(1), Term::int(2), Term::int(3)]);
        let (elems3, tail3) = l3.unpack_list(a).unwrap();
        assert_eq!(elems3.len(), 3);
        assert_eq!(elems3[0].unpack_int(a).unwrap(), 1);
        assert_eq!(elems3[1].unpack_int(a).unwrap(), 2);
        assert_eq!(elems3[2].unpack_int(a).unwrap(), 3);
        assert_eq!(tail3, &Term::NIL);

        // Non-list should error
        let not_list = Term::int(9);
        assert!(not_list.unpack_list(a).is_err());
    }

    #[test]
    fn unpack_tuple_any_and_fixed() {
        let a = &mut Arena::new();

        let t0 = Term::tuple(a, &[] as &[Term]);
        let t3 = Term::tuple(a, &[Term::int(1), Term::int(2), Term::int(3)]);

        // any arity
        let elems0 = t0.unpack_tuple_any(a).unwrap();
        assert!(elems0.is_empty());

        let elems3 = t3.unpack_tuple_any(a).unwrap();
        assert_eq!(elems3.len(), 3);
        assert_eq!(elems3[0].unpack_int(a).unwrap(), 1);
        assert_eq!(elems3[1].unpack_int(a).unwrap(), 2);
        assert_eq!(elems3[2].unpack_int(a).unwrap(), 3);

        // fixed arity
        let arr3 = t3.unpack_tuple::<3>(a).unwrap();
        assert_eq!(arr3[0].unpack_int(a).unwrap(), 1);
        assert_eq!(arr3[1].unpack_int(a).unwrap(), 2);
        assert_eq!(arr3[2].unpack_int(a).unwrap(), 3);

        // wrong arity should error
        assert!(t3.unpack_tuple::<2>(a).is_err());

        // non-tuple should error
        assert!(Term::int(1).unpack_tuple_any(a).is_err());
        assert!(Term::int(1).unpack_tuple::<0>(a).is_err());
    }

    #[test]
    fn unpack_atom_var_wrong_type_errs() {
        let a = &mut Arena::new();

        let not_atom = Term::int(1);
        let not_var = Term::str(a, "X");
        assert!(not_atom.atom_name(a).is_err());
        assert!(not_var.var_name(a).is_err());
    }

    #[test]
    fn unpack_func_wrong_type_errs() {
        let a = &mut Arena::new();

        // tuple is not a func
        let tup = Term::tuple(a, &[Term::int(1), Term::int(2)]);
        assert!(tup.func_name(a).is_err());
        assert!(tup.unpack_func::<2>(a, &[]).is_err());

        // atom can be unpacked with unpack_func* functions
        let at = Term::atom(a, "f");
        assert!(!at.unpack_func_any(a, &[]).is_err());
        assert!(!at.unpack_func::<0>(a, &[]).is_err());
    }

    #[test]
    fn fmt_nil_to_string() {
        let arena = Arena::new();
        let t = Term::NIL;
        assert_eq!(t.display(&arena).to_string(), "nil");
    }

    #[test]
    fn fmt_unit_format_macro() {
        let arena = Arena::new();
        let t = Term::UNIT;
        assert_eq!(format!("{}", t.display(&arena)), "unit");
    }

    #[test]
    fn fmt_int_positive() {
        let arena = Arena::new();
        let t = Term::int(42);
        assert_eq!(format!("{}", t.display(&arena)), "42");
    }

    #[test]
    fn fmt_int_negative_to_string() {
        let arena = Arena::new();
        let t = Term::int(-9001);
        assert_eq!(t.display(&arena).to_string(), "-9001");
    }

    #[test]
    fn fmt_str_quotes() {
        let mut arena = Arena::new();
        let t = Term::str(&mut arena, "hello");
        assert_eq!(format!("{}", t.display(&arena)), r#""hello""#);
    }

    #[test]
    fn fmt_str_with_escape_chars() {
        let mut arena = Arena::new();
        let t = Term::str(&mut arena, "a\nb\tc");
        assert_eq!(t.display(&arena).to_string(), "\"a\\nb\\tc\"");
    }

    #[test]
    fn fmt_date_epoch_zero() {
        let arena = Arena::new();
        // 0 ms -> 1970-01-01 00:00:00 UTC
        let t = Term::date(0);
        assert_eq!(
            format!("{}", t.display(&arena)),
            "date{1970-01-01T00:00:00+00:00}"
        );
    }

    #[test]
    fn fmt_date_epoch_ms_trunc_to_seconds() {
        let arena = Arena::new();
        let t = Term::date(1_234);
        assert_eq!(
            t.display(&arena).to_string(),
            "date{1970-01-01T00:00:01.234+00:00}"
        );
    }

    #[test]
    fn fmt_date_specific_moment() {
        let arena = Arena::new();
        let t = Term::date(1_727_525_530_123i64);
        assert_eq!(
            format!("{}", t.display(&arena)),
            "date{2024-09-28T12:12:10.123+00:00}"
        );
    }

    #[test]
    fn fmt_date_specific_moment_in_the_past() {
        let arena = Arena::new();
        let t = Term::date(-5_382_698_399_999i64);
        assert_eq!(
            format!("{}", t.display(&arena)),
            "date{1799-06-06T06:00:00.001+00:00}"
        );
    }

    #[test]
    fn fmt_write_into_string_buffer() {
        let arena = Arena::new();
        let t = Term::int(7);
        let mut buf = String::new();
        // write! returns fmt::Result; ensure it's Ok and content matches
        write!(&mut buf, "val={}", t.display(&arena)).expect("formatting failed");
        assert_eq!(buf, "val=7");
    }
}
