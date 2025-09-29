//! Copyright (c) 2005–2025 IKH Software, Inc. <support@ikhsoftware.com>
//!
//! Released under the terms of the GNU Lesser General Public License, version 3.0
//! or (at your option) any later version (LGPL-3.0-or-later).
//!
//! A lightweight, arena-backed representation of Prolog–like terms.
//!
//! This crate provides a compact [`Term`] type for representing Prolog-like
//! data structures, along with a typed arena [`Arena`] used to
//! intern atoms, variables, strings, binaries and compound terms.  The
//! underlying representation is designed around a fixed‐width 16
//! byte handle which carries both the tag and value of a term.
//!
//! The primary entry points are [`Arena`] (for allocating
//! interned data) and [`Term`] (the user visible term handle).  Terms
//! can be matched using the [`Term::view`] method which yields a
//! [`View`] that borrows from the underlying arena.  Equality and
//! ordering are well defined according to Prolog's standard order of
//! terms.  Users may construct lists and tuples conveniently via
//! macros exported from this crate.
//!
//! ## Example
//! ```rust
//! # use arena_terms::{Arena, func, IntoTerm, list, tuple, var, View};
//! // create an arena
//! let mut arena = Arena::new();
//!
//! // build some primitive terms
//! let a = arena.atom("hello");
//! let b = arena.real(3.14);
//! let c = arena.date(1_640_995_200_000i64);  // 2022-01-01T00:00:00Z
//!
//! // build a long list from an iterator
//! let xs = arena.list((0..1_000_000).map(|x| x as f64));
//!
//! // build a compound term using the func! macro
//! let term = func![
//!     "example";
//!     123,                // IntoTerm: integer
//!     "abc",              // IntoTerm: &str
//!     list![a, b, c, xs], // nested list (xs is shared)
//!     tuple!(b, a, xs),   // nested tuple (xs is shared)
//!     var!("X"),          // variable (implicit arena)
//!     => &mut arena
//! ];
//!
//! // inspect the resulting term
//! if let Ok(View::Func(ar, functor, args)) = term.view(&arena) {
//!     assert_eq!(functor.name(ar).unwrap(), "example");
//!     assert_eq!(args.len(), 5);
//!     // view nested terms recursively
//!     match args[2].view(ar).unwrap() {
//!         View::List(_, elems, _) => assert_eq!(elems.len(), 4),
//!         _ => unreachable!(),
//!     }
//! }
//! ```
//!

use core::fmt;
use smartstring::alias::String;
use std::borrow::Cow;
use std::cmp::Ordering;

// The following type definitions describe the internal representation
// of a term.  Rather than packing data into a single integer we use
// a tagged enum to store the various kinds of terms.  Each variant
// carries its associated data directly, for example a 64 bit integer
// for numeric types or a small inline buffer for short atoms and
// variables.  Long names or sequences store an index and length into
// the appropriate arena.

#[derive(Debug, Copy, Clone, PartialEq, PartialOrd)]
struct TinyArray {
    bytes: [u8; 14],
    len: u8,
}

#[derive(Debug, Copy, Clone, PartialEq, PartialOrd)]
struct Slice {
    epoch_id: EpochID,
    index: u32,
    len: u32,
}

/// Internal handle describing the kind of a term and storing its data.
///
/// Each variant stores the associated value directly.  The `repr(u8)`
/// attribute ensures the discriminant occupies a single byte, which
/// together with the payloads yields a `Term` size of 16 bytes on
/// 64‑bit targets.
#[derive(Debug, Copy, Clone, PartialEq, PartialOrd)]
#[repr(u8)]
enum Handle {
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
pub struct Term(Handle);

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

    /// Produce a [`View`] of this term that borrows from the given
    /// [`Arena`].  This method decodes any inlined bytes and
    /// dereferences indexes into the arena to yield structured
    /// references.  See [`View`] for details.
    #[inline]
    pub fn view<'a>(&'a self, arena: &'a Arena) -> Result<View<'a>, TermError> {
        match &self.0 {
            Handle::Int(i) => Ok(View::Int(*i)),
            Handle::Real(f) => Ok(View::Real(*f)),
            Handle::Date(d) => Ok(View::Date(*d)),
            Handle::Var(vs) => {
                let s_bytes = &vs.bytes[..vs.len as usize];
                let s = unsafe { core::str::from_utf8_unchecked(s_bytes) };
                Ok(View::Var(s))
            }
            Handle::VarRef(vr) => Ok(View::Var(unsafe {
                core::str::from_utf8_unchecked(
                    arena
                        .byte_slice(vr)
                        .map_err(|_| TermError::InvalidTerm(*self))?,
                )
            })),
            Handle::Atom(a) => {
                let s_bytes = &a.bytes[..a.len as usize];
                let s = unsafe { core::str::from_utf8_unchecked(s_bytes) };
                Ok(View::Atom(s))
            }
            Handle::AtomRef(ar) => Ok(View::Atom(unsafe {
                core::str::from_utf8_unchecked(
                    arena
                        .byte_slice(ar)
                        .map_err(|_| TermError::InvalidTerm(*self))?,
                )
            })),
            Handle::Str(ss) => {
                let s_bytes = &ss.bytes[..ss.len as usize];
                let s = unsafe { core::str::from_utf8_unchecked(s_bytes) };
                Ok(View::Str(s))
            }
            Handle::StrRef(sr) => Ok(View::Str(unsafe {
                core::str::from_utf8_unchecked(
                    arena
                        .byte_slice(sr)
                        .map_err(|_| TermError::InvalidTerm(*self))?,
                )
            })),
            Handle::Bin(bs) => {
                let b = &bs.bytes[..bs.len as usize];
                Ok(View::Bin(b))
            }
            Handle::BinRef(br) => Ok(View::Bin(
                arena
                    .byte_slice(br)
                    .map_err(|_| TermError::InvalidTerm(*self))?,
            )),
            Handle::FuncRef(fr) => {
                let slice = arena
                    .term_slice(fr)
                    .map_err(|_| TermError::InvalidTerm(*self))?;
                // Functor is the first element of the slice
                let functor = &slice[0];
                let args = &slice[1..];
                Ok(View::Func(arena, functor, args))
            }
            Handle::ListRef(lr) => {
                let slice = arena
                    .term_slice(lr)
                    .map_err(|_| TermError::InvalidTerm(*self))?;
                Ok(View::List(arena, slice, &Term::NIL))
            }
            Handle::ListCRef(lr) => {
                let slice = arena
                    .term_slice(lr)
                    .map_err(|_| TermError::InvalidTerm(*self))?;
                let last = slice.len() - 1;
                Ok(View::List(arena, &slice[..last], &slice[last]))
            }
            Handle::TupleRef(tr) => {
                let slice = arena
                    .term_slice(tr)
                    .map_err(|_| TermError::InvalidTerm(*self))?;
                Ok(View::Tuple(arena, slice))
            }
        }
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

impl fmt::Debug for View<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            View::Int(i) => f.debug_tuple("Int").field(&i).finish(),
            View::Real(r) => f.debug_tuple("Real").field(&r).finish(),
            View::Date(d) => f.debug_tuple("Date").field(&d).finish(),
            View::Var(v) => f.debug_tuple("Var").field(&v).finish(),
            View::Atom(a) => f.debug_tuple("Atom").field(&a).finish(),
            View::Str(s) => f.debug_tuple("Str").field(&s).finish(),
            View::Bin(b) => f.debug_tuple("Bin").field(&b).finish(),
            View::Func(a, fr, ts) => f
                .debug_tuple("Func")
                .field(&a.arena_id)
                .field(&fr)
                .field(&ts.iter().map(|t| t.view(a)).collect::<Vec<_>>())
                .finish(),
            View::List(a, ts, tail) => f
                .debug_tuple("List")
                .field(&a.arena_id)
                .field(&ts.iter().map(|t| t.view(a)).collect::<Vec<_>>())
                .field(&tail.view(a))
                .finish(),
            View::Tuple(a, ts) => f
                .debug_tuple("Tuple")
                .field(&a.arena_id)
                .field(&ts.iter().map(|t| t.view(a)).collect::<Vec<_>>())
                .finish(),
        }
    }
}

/// A borrowed view into the interned contents of a [`Term`].
///
/// Use [`Term::view`] to obtain a view.  Each variant of [`View`]
/// represents the decoded form of a term and borrows any data
/// referenced from the [`Arena`] or the term handle itself.  No
/// allocations are performed when constructing a `View`; instead
/// references into the underlying storage are returned directly.  The
/// lifetime `'a` binds the returned references to both the borrowed
/// `Term` and the supplied `Arena`.
#[derive(Clone, Copy)]
pub enum View<'a> {
    /// An integer value.
    Int(i64),
    /// A floating point value.
    Real(f64),
    /// A date value (milliseconds since the Unix epoch).
    Date(i64),
    /// A variable name borrowed from the term or arena.
    Var(&'a str),
    /// An atom name borrowed from the term or arena.
    Atom(&'a str),
    /// A UTF‑8 string borrowed from the term or arena.
    Str(&'a str),
    /// A binary slice borrowed from the term or arena.
    Bin(&'a [u8]),
    /// A compound term view containing the functor name and a slice
    /// of arguments.  Both the functor and the argument slice are
    /// borrowed; the arguments themselves are `Term` handles owned
    /// by the arena.
    Func(&'a Arena, &'a Term, &'a [Term]),
    /// A list view containing a slice of the list elements
    /// and a reference to the tail term. The element slice and the tail are
    /// borrowed; the elements themselves are `Term` handles owned by the arena.
    /// The tail of a proper list will always reference Term::NIL.
    List(&'a Arena, &'a [Term], &'a Term),
    /// A tuple view containing a slice of the tuple elements.
    /// The element slice are borrowed; the elements
    /// themselves are `Term` handles owned by the arena.
    Tuple(&'a Arena, &'a [Term]),
}

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
    arena_id: ArenaID,

    /// Index into the buffers of alive epochs.
    /// Always points to the "current" epoch (latest allocations).
    current_epoch: usize,

    /// Randomly generated identifiers, one per epoch.
    /// Every handle (e.g., term, func, var) that references this arena
    /// carries the epoch ID that was current at allocation time.
    /// When a handle is later resolved, the epoch ID is checked to
    /// ensure it still belongs to the same arena instance.
    epoch_ids: [EpochID; MAX_LIVE_EPOCHS],

    /// Storage for interned atoms, variables, strings, and binary blobs.
    /// Data are appended sequentially in the last active epoch.
    bytes: Vec<u8>,

    /// For each epoch, the starting offset into `bytes`.
    /// Used to "rewind" or reclaim all data belonging to an expired epoch.
    byte_start_by_epoch: [usize; MAX_LIVE_EPOCHS],

    /// Storage for compound terms (structured values).
    /// Terms are appended sequentially in the last active epoch.
    /// Each term is represented as a contiguous slice:
    ///   [functor_atom, arg1, arg2, …]
    /// The `Func` handle encodes both the slice’s starting index and length.
    terms: Vec<Term>,

    /// For each epoch, the starting index into `terms`.
    /// Used to drop/pick up all terms from an expired epoch in bulk.
    term_start_by_epoch: [usize; MAX_LIVE_EPOCHS],
}

pub const MAX_LIVE_EPOCHS: usize = 8;

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct EpochID(u32); // Random Epoch ID

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
struct ArenaID(u32); // Random Arena ID

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

    /// Produce a [`View`] of the given `term` that borrows from
    /// this [`Arena`].  This method decodes any inlined bytes and
    /// dereferences indexes into the arena to yield structured
    /// references.  See [`View`] for details.
    #[inline]
    pub fn view<'a>(&'a self, term: &'a Term) -> Result<View<'a>, TermError> {
        term.view(self)
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
    fn intern_str(&mut self, s: &str) -> Slice {
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
    fn intern_bytes(&mut self, bytes: &[u8]) -> Slice {
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
    fn intern_func(
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
    fn intern_seq(&mut self, terms: impl IntoIterator<Item = impl IntoTerm>) -> Slice {
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
    fn intern_seq_plus_one(
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
    fn byte_slice<'a>(&'a self, slice: &Slice) -> Result<&'a [u8], InternalTermError> {
        self.verify_byte_slice(slice)?;
        Ok(&self.bytes[(slice.index as usize)..((slice.index + slice.len) as usize)])
    }

    /// Borrow a slice of terms comprising a compound term.
    #[inline]
    fn term_slice<'a>(&'a self, slice: &Slice) -> Result<&'a [Term], InternalTermError> {
        self.verify_term_slice(slice)?;
        Ok(&self.terms[(slice.index as usize)..((slice.index + slice.len) as usize)])
    }
}

/// Errors that may occur when constructing terms or interacting with arena.
#[derive(Debug, Clone)]
pub enum TermError {
    InvalidTerm(Term),
    LiveEpochsExceeded,
    InvalidEpoch(EpochID),
    MissingFunctor,
    InvalidFunctor(Term),
    UnexpectedKind {
        expected: &'static str,
        found: &'static str,
    },
    UnexpectedArity {
        expected: usize,
        found: usize,
    },
    UnexpectedName(Term),
}

impl fmt::Display for TermError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TermError::InvalidTerm(term) => {
                write!(f, "Invalid term {:?}", term)
            }
            TermError::LiveEpochsExceeded => {
                write!(f, "Epoch overflow")
            }
            TermError::InvalidEpoch(epoch_id) => {
                write!(f, "Invalid epoch {:?}", epoch_id)
            }
            TermError::MissingFunctor => {
                write!(f, "Missing functor")
            }
            TermError::InvalidFunctor(term) => {
                write!(f, "Invalid functor {:?}", term)
            }
            TermError::UnexpectedKind { expected, found } => {
                write!(f, "Type mismatch: expected {}, found {}", expected, found)
            }
            TermError::UnexpectedArity { expected, found } => {
                write!(f, "Arity mismatch: expected {}, found {}", expected, found)
            }
            TermError::UnexpectedName(term) => {
                write!(f, "Unexpected name in {:?}", term)
            }
        }
    }
}

/// Internal errors that may occur when constructing terms or interacting with arena.
#[derive(Debug, Clone)]
enum InternalTermError {
    InvalidEpoch(EpochID),
    InvalidSlice(Slice),
}

impl fmt::Display for InternalTermError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            InternalTermError::InvalidEpoch(epoch_id) => {
                write!(f, "Invalid epoch {:?}", epoch_id)
            }
            InternalTermError::InvalidSlice(slice) => {
                write!(f, "Invalid slice {:?}", slice)
            }
        }
    }
}

impl std::error::Error for TermError {}

impl<'a> PartialEq for View<'a> {
    fn eq(&self, other: &Self) -> bool {
        let order_a = kind_order(self);
        let order_b = kind_order(other);
        if order_a != order_b {
            return false;
        }
        match (self, other) {
            // Numbers: compare by numeric value irrespective of the exact type.
            (
                View::Int(_) | View::Real(_) | View::Date(_),
                View::Int(_) | View::Real(_) | View::Date(_),
            ) => {
                let a = numeric_value(self);
                let b = numeric_value(other);
                a == b
            }
            // Variables
            (View::Var(a), View::Var(b)) => a == b,
            // Atoms
            (View::Atom(a), View::Atom(b)) => a == b,
            // Strings
            (View::Str(a), View::Str(b)) => a == b,
            // Binaries
            (View::Bin(a), View::Bin(b)) => a == b,
            // Compounds: compare by length (arity+1) then by slice index.
            (View::Func(arena_a, functor_a, args_a), View::Func(arena_b, functor_b, args_b)) => {
                if args_a.len() != args_b.len() {
                    return false;
                }
                if functor_a != functor_b {
                    return false;
                }
                args_a.iter().zip(args_b.iter()).all(|(a, b)| {
                    a.view(arena_a).expect("arena mismatch")
                        == b.view(arena_b).expect("arena mismatch")
                })
            }
            (View::List(arena_a, args_a, tail_a), View::List(arena_b, args_b, tail_b)) => {
                if args_a.len() != args_b.len() {
                    return false;
                }
                args_a.iter().zip(args_b.iter()).all(|(a, b)| {
                    a.view(arena_a).expect("arena mismatch")
                        == b.view(arena_b).expect("arena mismatch")
                }) && tail_a.view(arena_a).expect("arena mismatch")
                    == tail_b.view(arena_b).expect("arena mismatch")
            }
            (View::Tuple(arena_a, args_a), View::Tuple(arena_b, args_b)) => {
                if args_a.len() != args_b.len() {
                    return false;
                }
                args_a.iter().zip(args_b.iter()).all(|(a, b)| {
                    a.view(arena_a).expect("arena mismatch")
                        == b.view(arena_b).expect("arena mismatch")
                })
            }
            _ => unreachable!(),
        }
    }
}

impl<'a> Eq for View<'a> {}

impl core::cmp::PartialOrd for View<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl core::cmp::Ord for View<'_> {
    fn cmp(&self, other: &Self) -> Ordering {
        let order_a = kind_order(self);
        let order_b = kind_order(other);
        if order_a != order_b {
            return order_a.cmp(&order_b);
        }
        match (self, other) {
            // Numbers: compare by numeric value irrespective of the exact type.
            (
                View::Int(_) | View::Real(_) | View::Date(_),
                View::Int(_) | View::Real(_) | View::Date(_),
            ) => {
                let a = numeric_value(self);
                let b = numeric_value(other);
                a.total_cmp(&b)
            }
            // Variables
            (View::Var(a), View::Var(b)) => a.cmp(b),
            // Atoms
            (View::Atom(a), View::Atom(b)) => a.cmp(b),
            // Strings
            (View::Str(a), View::Str(b)) => a.cmp(b),
            // Binaries
            (View::Bin(a), View::Bin(b)) => a.cmp(b),
            // Compounds: compare by length (arity+1) then by slice index.
            (View::Func(arena_a, functor_a, args_a), View::Func(arena_b, functor_b, args_b)) => {
                let ord = args_a.len().cmp(&args_b.len());
                if ord != Ordering::Equal {
                    return ord;
                }
                let ord = functor_a
                    .view(arena_a)
                    .expect("arena mismatch")
                    .cmp(&functor_b.view(arena_b).expect("arena mismatch"));
                if ord != Ordering::Equal {
                    return ord;
                }
                for (arg_a, arg_b) in args_a.iter().zip(args_b.iter()).map(|(a, b)| {
                    (
                        a.view(arena_a).expect("arena mismatch"),
                        b.view(arena_b).expect("arena mismatch"),
                    )
                }) {
                    let ord = arg_a.cmp(&arg_b);
                    if ord != Ordering::Equal {
                        return ord;
                    }
                }
                Ordering::Equal
            }
            (View::List(arena_a, args_a, tail_a), View::List(arena_b, args_b, tail_b)) => {
                let ord = args_a.len().cmp(&args_b.len());
                if ord != Ordering::Equal {
                    return ord;
                }
                for (arg_a, arg_b) in args_a.iter().zip(args_b.iter()).map(|(a, b)| {
                    (
                        a.view(arena_a).expect("arena mismatch"),
                        b.view(arena_b).expect("arena mismatch"),
                    )
                }) {
                    let ord = arg_a.cmp(&arg_b);
                    if ord != Ordering::Equal {
                        return ord;
                    }
                }
                tail_a
                    .view(arena_a)
                    .expect("arena mismatch")
                    .cmp(&tail_b.view(arena_b).expect("arena mismatch"))
            }
            (View::Tuple(arena_a, args_a), View::Tuple(arena_b, args_b)) => {
                let ord = args_a.len().cmp(&args_b.len());
                if ord != Ordering::Equal {
                    return ord;
                }
                for (arg_a, arg_b) in args_a.iter().zip(args_b.iter()).map(|(a, b)| {
                    (
                        a.view(arena_a).expect("arena mismatch"),
                        b.view(arena_b).expect("arena mismatch"),
                    )
                }) {
                    let ord = arg_a.cmp(&arg_b);
                    if ord != Ordering::Equal {
                        return ord;
                    }
                }
                Ordering::Equal
            }

            _ => unreachable!(),
        }
    }
}

/// Compute the kind order used for comparing terms of different kinds.
/// According to Prolog standard order: variables < numbers < atoms < strings
/// < binaries < compounds.
fn kind_order(t: &View) -> u8 {
    match t {
        View::Var(_) => 0,
        View::Int(_) => 1,
        View::Date(_) => 2,
        View::Real(_) => 3,
        View::Atom(_) => 4,
        View::Str(_) => 5,
        View::Func(_, _, _) => 6,
        View::Tuple(_, _) => 7,
        View::List(_, _, _) => 8,
        View::Bin(_) => 9,
    }
}

/// Extract a numeric value from a term for ordering purposes.  All
/// numeric kinds (int, real and date) are converted to `f64` for
/// comparison.  `Date` values use their millisecond representation as
/// the numeric value.
fn numeric_value(t: &View) -> f64 {
    match t {
        View::Int(i) => *i as f64,
        View::Real(f) => *f,
        View::Date(d) => *d as f64,
        _ => unreachable!(),
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

/// A wrapper that ties together a [`Term`] and its [`Arena`], forming the
/// basis for configurable pretty-printing. This type is designed as the
/// foundation on which flexible formatting and printing of terms will be built.
///
/// It already implements [`fmt::Display`], so you can seamlessly use it with
/// standard formatting macros (`format!`, `println!`, etc.) to render
/// terms. In the future, it will also support additional, customizable
/// formatting options for advanced pretty-printing.
///
/// ### Example
/// ```rust
/// use arena_terms::{Term, Arena, func, IntoTerm};
/// let mut arena = Arena::new();
/// let term = func!("foo"; 1, "hello, world!" => &mut arena);
///
/// println!("{}", term.display(&arena));
/// ```
///
/// Construct instances via [`Term::display`] or [`Arena::display`].
pub struct TermDisplay<'a> {
    /// The interned term to display.
    term: &'a Term,
    /// The arena where the term is stored.
    arena: &'a Arena,
}

impl Term {
    /// Return a [`TermDisplay`] suitable for formatting with [`fmt::Display`].
    ///
    /// Use this method when you want to render a term:
    ///
    /// ```ignore
    /// println!("{}", term.display(&arena));
    /// ```
    #[inline]
    pub fn display<'a>(&'a self, arena: &'a Arena) -> TermDisplay<'a> {
        TermDisplay { term: self, arena }
    }
}

/// Implements [`fmt::Display`] for [`TermDisplay`], enabling it to be
/// formatted and printed with standard formatting macros.
impl<'a> fmt::Display for TermDisplay<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn is_unquoted_atom(s: &str) -> bool {
            let mut chars = s.chars();
            match chars.next() {
                Some(c) if c.is_ascii_lowercase() => {}
                _ => return false,
            }
            chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
        }

        fn write_atom(f: &mut fmt::Formatter<'_>, arena: &Arena, functor: &Term) -> fmt::Result {
            let s = arena.atom_name(functor).map_err(|_e| fmt::Error)?;
            write_atom_str(f, s)
        }

        fn write_atom_str(f: &mut fmt::Formatter<'_>, s: &str) -> fmt::Result {
            if s.is_empty() || !is_unquoted_atom(s) {
                let escaped = s.replace('\'', "\\'");
                write!(f, "'{}'", escaped)
            } else {
                write!(f, "{}", s)
            }
        }

        fn write_str_quoted(f: &mut fmt::Formatter<'_>, s: &str) -> fmt::Result {
            let mut out = String::new();
            out.push('"');
            for ch in s.chars() {
                match ch {
                    '\\' => out.push_str("\\\\"),
                    '"' => out.push_str("\\\""),
                    '\n' => out.push_str("\\n"),
                    '\r' => out.push_str("\\r"),
                    '\t' => out.push_str("\\t"),
                    c if c.is_control() => out.push_str(&format!("\\x{:02X}\\", c as u32)),
                    c => out.push(c),
                }
            }
            out.push('"');
            f.write_str(&out)
        }

        fn epoch_to_date_string(epoch_ms: i64, fmt: Option<&str>) -> String {
            use chrono::{DateTime, Utc};

            let secs = epoch_ms.div_euclid(1000);
            let nsecs = (epoch_ms.rem_euclid(1000) * 1_000_000) as u32;

            let dt_utc = DateTime::<Utc>::from_timestamp(secs, nsecs).unwrap();

            String::from(match fmt {
                None => dt_utc.to_rfc3339(),
                Some(layout) => dt_utc.format(layout).to_string(),
            })
        }

        fn write_args(f: &mut fmt::Formatter<'_>, arena: &Arena, args: &[Term]) -> fmt::Result {
            for (i, t) in args.iter().enumerate() {
                if i > 0 {
                    f.write_str(", ")?;
                }
                write!(f, "{}", t.display(arena))?;
            }
            Ok(())
        }

        match self.term.view(self.arena).map_err(|_e| fmt::Error)? {
            View::Int(i) => write!(f, "{i}"),
            View::Real(r) => {
                if r.fract() == 0.0 {
                    write!(f, "{:.1}", r)
                } else {
                    write!(f, "{}", r)
                }
            }
            View::Date(epoch) => write!(f, "date({})", epoch_to_date_string(epoch, None)),
            View::Str(s) => write_str_quoted(f, s),
            View::Bin(bytes) => {
                write!(f, "hex{{")?;
                for b in bytes {
                    write!(f, "{:02X}", b)?;
                }
                write!(f, "}}")
            }
            View::Atom(a) => write_atom_str(f, a),
            View::Var(v) => write!(f, "{}", v),

            View::Func(ar, functor, args) => {
                if args.is_empty() {
                    return write!(f, "/* invalid Func */");
                }
                write_atom(f, ar, functor)?;
                write!(f, "(")?;
                write_args(f, ar, args)?;
                write!(f, ")")
            }

            View::Tuple(ar, items) => {
                if items.is_empty() {
                    write!(f, "()")
                } else {
                    write!(f, "(")?;
                    write_args(f, ar, items)?;
                    write!(f, ")")
                }
            }

            View::List(ar, items, tail) => {
                if items.is_empty() {
                    write!(f, "[]")
                } else {
                    write!(f, "[")?;
                    write_args(f, ar, items)?;
                    if *tail != Term::NIL {
                        f.write_str(" | ")?;
                        write!(f, "{}", tail.display(ar))?;
                    }
                    write!(f, "]")
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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
    fn view_size_is_40_bytes() {
        assert_eq!(core::mem::size_of::<View>(), 40);
    }

    #[test]
    fn option_view_size_is_40_bytes() {
        assert_eq!(core::mem::size_of::<Option<View>>(), 40);
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
            "foo(nil, unit, point(1, 2.0, date(1970-01-01T00:00:01+00:00), hello, Hello, \"A str\\ning. Longer string.\", [hello, Hello, \"A str\\ning. Longer string.\"], (\"A str\\ning. Longer string.\", \"A str\\ning. Longer string.\")), point(1, 2.0, date(1970-01-01T00:00:01+00:00), hello, Hello, \"A str\\ning. Longer string.\", [hello, Hello, \"A str\\ning. Longer string.\"], (\"A str\\ning. Longer string.\", \"A str\\ning. Longer string.\")), nil, [1, 2.0 | date(1970-01-01T00:00:01+00:00)])"
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
            "date(1970-01-01T00:00:00+00:00)"
        );
    }

    #[test]
    fn fmt_date_epoch_ms_trunc_to_seconds() {
        let arena = Arena::new();
        let t = Term::date(1_234);
        assert_eq!(
            t.display(&arena).to_string(),
            "date(1970-01-01T00:00:01.234+00:00)"
        );
    }

    #[test]
    fn fmt_date_specific_moment() {
        let arena = Arena::new();
        let t = Term::date(1_727_525_530_123i64);
        assert_eq!(
            format!("{}", t.display(&arena)),
            "date(2024-09-28T12:12:10.123+00:00)"
        );
    }

    #[test]
    fn fmt_date_specific_moment_in_the_past() {
        let arena = Arena::new();
        let t = Term::date(-5_382_698_399_999i64);
        assert_eq!(
            format!("{}", t.display(&arena)),
            "date(1799-06-06T06:00:00.001+00:00)"
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
