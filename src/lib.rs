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
//!
//! ```rust
//! use arena_terms::{Arena, func, IntoTerm, list, tuple, var, View};
//!
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
//!     assert_eq!(functor, "example");
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

#[derive(Debug, Copy, Clone, PartialEq)]
struct TinyArray {
    bytes: [u8; 14],
    len: u8,
}

#[derive(Debug, Copy, Clone, PartialEq)]
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
#[repr(u8)]
#[derive(Copy, Clone, PartialEq)]
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
#[derive(Copy, Clone, PartialEq)]
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

    /// Constructs a new list. A list is represented as a compound term
    /// with the functor `list`.
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
    /// a compound term with the functor `listc` and additional argument.
    /// If `terms` is empty, returns `nil`.
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

    /// Constructs a new tuple. A tuple is represented as a compound term
    /// with the functor `tuple`.
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
                let functor = match &slice[0].0 {
                    Handle::Atom(a) => {
                        let s_bytes = &a.bytes[..a.len as usize];
                        unsafe { core::str::from_utf8_unchecked(s_bytes) }
                    }
                    Handle::AtomRef(ar2) => unsafe {
                        core::str::from_utf8_unchecked(
                            arena
                                .byte_slice(ar2)
                                .map_err(|_| TermError::InvalidTerm(*self))?,
                        )
                    },
                    _ => panic!("invalid functor"),
                };
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

    #[inline]
    pub fn is_func(&self) -> bool {
        matches!(self.0, Handle::FuncRef(_))
    }

    #[inline]
    pub fn is_list(&self) -> bool {
        matches!(self.0, Handle::ListRef(_)) || *self == Self::NIL
    }

    #[inline]
    pub fn is_listc(&self) -> bool {
        matches!(self.0, Handle::ListCRef(_))
    }

    #[inline]
    pub fn is_tuple(&self) -> bool {
        matches!(self.0, Handle::TupleRef(_)) || *self == Self::UNIT
    }

    #[inline]
    pub fn is_int(&self) -> bool {
        matches!(self.0, Handle::Int(_))
    }

    #[inline]
    pub fn is_real(&self) -> bool {
        matches!(self.0, Handle::Real(_))
    }

    #[inline]
    pub fn is_date(&self) -> bool {
        matches!(self.0, Handle::Date(_))
    }

    #[inline]
    pub fn is_atom(&self) -> bool {
        matches!(self.0, Handle::Atom(_) | Handle::AtomRef(_))
    }

    #[inline]
    pub fn is_var(&self) -> bool {
        matches!(self.0, Handle::Var(_) | Handle::VarRef(_))
    }

    #[inline]
    pub fn is_number(&self) -> bool {
        matches!(self.0, Handle::Int(_) | Handle::Real(_) | Handle::Date(_))
    }

    #[inline]
    pub fn is_str(&self) -> bool {
        matches!(self.0, Handle::Str(_) | Handle::StrRef(_))
    }

    #[inline]
    pub fn is_bin(&self) -> bool {
        matches!(self.0, Handle::Bin(_) | Handle::BinRef(_))
    }

    #[inline]
    pub fn arity(&self) -> usize {
        match &self.0 {
            Handle::FuncRef(Slice { len: n, .. }) => (n - 1) as usize,
            _ => 0,
        }
    }
}

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
    Func(&'a Arena, &'a str, &'a [Term]),
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
/// use arena_terms::Arena;
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

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
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

    pub fn list(&mut self, terms: impl IntoIterator<Item = impl IntoTerm>) -> Term {
        Term::list(self, terms)
    }

    pub fn listc(
        &mut self,
        terms: impl IntoIterator<Item = impl IntoTerm>,
        tail: impl IntoTerm,
    ) -> Term {
        Term::listc(self, terms, tail)
    }

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

    /// Intern a UTF‑8 string into the arena and return its slice
    /// descriptor.  Strings are stored in a contiguous bump vector.
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
    fn byte_slice<'a>(&'a self, slice: &Slice) -> Result<&'a [u8], InternalTermError> {
        self.verify_byte_slice(slice)?;
        Ok(&self.bytes[(slice.index as usize)..((slice.index + slice.len) as usize)])
    }

    /// Borrow a slice of terms comprising a compound term.
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
                let ord = functor_a.cmp(functor_b);
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn term_size_is_16_bytes() {
        assert_eq!(core::mem::size_of::<Term>(), 16);
    }

    #[test]
    fn option_term_size_is_16_bytes() {
        assert_eq!(core::mem::size_of::<Option<Term>>(), 16);
    }

    #[test]
    fn view_size_is_32_bytes() {
        assert_eq!(core::mem::size_of::<View>(), 48);
    }

    #[test]
    fn option_view_size_is_32_bytes() {
        assert_eq!(core::mem::size_of::<Option<View>>(), 48);
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
    fn compound_construction() {
        let mut arena = Arena::new();
        let a = Term::int(1);
        let b = Term::real(2.0);
        let c = Term::date(1000);
        let d = Term::atom(&mut arena, "hello");
        let e = Term::var(&mut arena, "Hello, hello, world!");
        let f = Term::str(&mut arena, "A str\ning.");
        let g = list![d, e, f => &mut arena];
        let h = tuple!(f => &mut arena);
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
            assert_eq!(functor, "foo");
            assert_eq!(p.arity(), 6);
            assert_eq!(args.len(), 6);
        } else {
            panic!("unexpected view");
        }
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
            assert_eq!(functor, "foo");
            assert_eq!(args.len(), 2);
        }
        if let Ok(View::Func(_, functor, args)) = y.view(&a) {
            assert_eq!(functor, "foo");
            assert_eq!(args.len(), 2);
        }
    }
}
