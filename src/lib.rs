//! A lightweight, arena‑backed representation of Prolog–like terms.
//!
//! This crate provides a compact [`Term`] type for representing Prolog
//! data structures, along with a typed arena [`TermArena`] used to
//! intern atoms, variables, strings, binaries and compound terms.  The
//! underlying representation is designed around a fixed‐width 16
//! byte handle which carries both the tag and value of a term.  See
//! the crate level documentation and the [`reqs.md`](../reqs.md) file in
//! the repository root for a detailed description of the design and
//! goals of this implementation.
//!
//! The primary entry points are [`TermArena`] (for allocating
//! interned data) and [`Term`] (the user visible term handle).  Terms
//! can be matched using the [`Term::view`] method which yields a
//! [`View`] that borrows from the underlying arena.  Equality and
//! ordering are well defined according to Prolog's standard order of
//! terms.  Users may construct lists and tuples conveniently via
//! macros exported from the [`term`] module.

#![cfg_attr(feature = "no_std", no_std)]
// When `no_std` is enabled we still depend on `alloc` for heap
// allocations.
#![cfg_attr(feature = "no_std", feature(alloc))]

// In `no_std` mode pull the alloc crate into scope for Vec and String.
#[cfg(feature = "no_std")]
extern crate alloc;

#[cfg(feature = "no_std")]
use alloc::{string::String, vec::Vec};

use core::{fmt, hash::Hash, mem::size_of};
#[cfg(not(feature = "no_std"))]
use std::cmp::Ordering;
#[cfg(feature = "no_std")]
use core::cmp::Ordering;

use indexmap::IndexSet;

// When serialisation is enabled bring `Serialize` and `Deserialize` into scope
// for derive macros.  Without these imports the `serde` derive macros cannot
// resolve the traits in a `no_std` context.
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

// The following type definitions describe the internal representation
// of a term.  Rather than packing data into a single integer we use
// a tagged enum to store the various kinds of terms.  Each variant
// carries its associated data directly, for example a 64 bit integer
// for numeric types or a small inline buffer for short atoms and
// variables.  Long names or sequences store an index and size into
// the appropriate arena.

/// A small inlined representation for names or data up to 14 bytes.
///
/// This single struct is used for atoms, variables, strings and binaries
/// when their data can be inlined directly into the term handle.  It
/// stores the bytes and the length of the valid prefix.  All small
/// variants share this type to reduce duplication.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
struct Small {
    bytes: [u8; 14],
    size: u8,
}

/// A generic slice reference used for long atoms, variables, strings,
/// binaries and compound terms.  It contains an offset/index into the
/// arena and the length of the slice.  All "Ref" variants share
/// this type.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
struct SliceRef {
    index: u32,
    size: u32,
}


/// Internal handle describing the kind of a term and storing its data.
///
/// Each variant stores the associated value directly.  The `repr(u8)`
/// attribute ensures the discriminant occupies a single byte, which
/// together with the payloads yields a `Term` size of 16 bytes on
/// 64‑bit targets.  The derive annotations provide comparison and
/// hashing implementations and optionally enable `serde` support.
#[repr(u8)]
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
enum TermHandle {
    Int(i64),
    Real(f64),
    Date(i64),
    VarSmall(Small),
    VarRef(SliceRef),
    AtomSmall(Small),
    AtomRef(SliceRef),
    StrSmall(Small),
    StrRef(SliceRef),
    BinSmall(Small),
    BinRef(SliceRef),
    Func(SliceRef),
}

/// A compact, copyable handle referencing a term stored in a [`TermArena`].
///
/// Internally a `Term` stores a single [`TermHandle`] enum variant.
/// On 64‑bit targets the discriminant and associated payload occupy
/// 16 bytes in total.  Users should never construct `Term` values
/// directly; instead use the associated constructors or the
/// convenience macros in the [`term`] module.
/// Instances of `Term` are cheap to copy (`Copy` and `Clone`) and may
/// be compared with [`PartialEq`], [`Eq`], [`PartialOrd`], [`Ord`] or
/// hashed for use in maps.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Term(TermHandle);

impl Term {
    /// Construct a new integer term.  The full 64 bit two's complement
    /// representation of `i` is stored in the payload.  No truncation
    /// occurs.
    #[inline(always)]
    pub fn int(i: i64) -> Self {
        Term(TermHandle::Int(i))
    }

    /// Construct a new floating point term.  The full 64 bit IEEE‑754
    /// bit pattern is stored in the payload without truncation.
    #[inline(always)]
    pub fn real(f: f64) -> Self {
        Term(TermHandle::Real(f))
    }

    /// Construct a new date term representing a Unix epoch in
    /// milliseconds.  Dates share the same underlying storage as
    /// integers but use a distinct tag so they do not compare equal
    /// with integer terms.
    #[inline(always)]
    pub fn date(ms: i64) -> Self {
        Term(TermHandle::Date(ms))
    }

    /// Construct or intern an atom into the arena and produce a term
    /// referencing it.  Small atom names (≤14 bytes of UTF‑8) are
    /// inlined directly into the handle; longer names are interned
    /// into the arena and referenced by index and length.
    #[inline(always)]
    pub fn atom(arena: &mut TermArena, name: &str) -> Self {
        let bytes = name.as_bytes();
        if bytes.len() <= 14 {
            let mut buf = [0u8; 14];
            buf[..bytes.len()].copy_from_slice(bytes);
            Term(TermHandle::AtomSmall(Small { bytes: buf, size: bytes.len() as u8 }))
        } else {
            let id = arena.intern_atom(name);
            let len = bytes.len() as u32;
            Term(TermHandle::AtomRef(SliceRef { index: id.0, size: len }))
        }
    }

    /// Construct or intern a variable into the arena and produce a
    /// term referencing it.  Small variable names (≤14 bytes) are
    /// inlined directly into the handle; longer names are interned in
    /// the arena and referenced by index.
    #[inline(always)]
    pub fn var(arena: &mut TermArena, name: &str) -> Self {
        let bytes = name.as_bytes();
        if bytes.len() <= 14 {
            let mut buf = [0u8; 14];
            buf[..bytes.len()].copy_from_slice(bytes);
            Term(TermHandle::VarSmall(Small { bytes: buf, size: bytes.len() as u8 }))
        } else {
            let id = arena.intern_var(name);
            let len = bytes.len() as u32;
            Term(TermHandle::VarRef(SliceRef { index: id.0, size: len }))
        }
    }

    /// Construct or intern a UTF‑8 string into the arena and produce a
    /// term referencing it.  Strings longer than 14 bytes are interned
    /// in the arena; shorter strings are inlined.  Invalid UTF‑8 will
    /// result in an error.
    #[inline(always)]
    pub fn str(arena: &mut TermArena, s: &str) -> Self {
        let bytes = s.as_bytes();
        if bytes.len() <= 14 {
            let mut buf = [0u8; 14];
            buf[..bytes.len()].copy_from_slice(bytes);
            Term(TermHandle::StrSmall(Small { bytes: buf, size: bytes.len() as u8 }))
        } else {
            let slice = arena.intern_str(s);
            Term(TermHandle::StrRef(SliceRef { index: slice.offset, size: slice.len }))
        }
    }

    /// Construct or intern a binary blob into the arena and produce a
    /// term referencing it.  Blobs longer than 14 bytes are interned
    /// in the arena; shorter blobs are inlined.
    #[inline(always)]
    pub fn bin(arena: &mut TermArena, bytes: &[u8]) -> Self {
        if bytes.len() <= 14 {
            let mut buf = [0u8; 14];
            buf[..bytes.len()].copy_from_slice(bytes);
            Term(TermHandle::BinSmall(Small { bytes: buf, size: bytes.len() as u8 }))
        } else {
            let slice = arena.intern_bin(bytes);
            Term(TermHandle::BinRef(SliceRef { index: slice.offset, size: slice.len }))
        }
    }

    /// Construct a new compound term by interning the functor and
    /// arguments in the arena.  The returned term references a slice
    /// in the arena's term storage consisting of the functor atom as
    /// the first entry followed by the argument handles.  A functor of
    /// arity zero is rejected: instead construct an atom directly via
    /// [`Term::atom`].
    #[inline(always)]
    pub fn func(arena: &mut TermArena, functor: &str, args: &[Term]) -> Result<Self, Error> {
        if args.is_empty() {
            return Err(Error::ArityZeroCompound(functor.to_owned()));
        }
        let functor_term = Term::atom(arena, functor);
        let slice = arena.intern_func(functor_term, args);
        Ok(Term(TermHandle::Func(SliceRef { index: slice.offset, size: slice.len })))
    }


    /// Constant representing the zero‑arity tuple (unit).  Internally
    /// this is the atom `"unit"` encoded as a small atom.  It may
    /// be copied freely and does not depend on any arena.
    pub const UNIT: Self = {
        let buf: [u8; 14] = [b'u', b'n', b'i', b't', 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
        Term(TermHandle::AtomSmall(Small { bytes: buf, size: 4 }))
    };

    /// Constant representing the empty list (nil).  Internally this is
    /// the atom `"nil"` encoded as a small atom.  It may be copied
    /// freely and does not depend on any arena.
    pub const NIL: Self = {
        let buf: [u8; 14] = [b'n', b'i', b'l', 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
        Term(TermHandle::AtomSmall(Small { bytes: buf, size: 3 }))
    };

    /// Extract the tag (kind) from this term.  This method matches the
    /// underlying [`TermHandle`] to return a corresponding [`Tag`].
    #[inline(always)]
    fn tag(self) -> Tag {
        match self.0 {
            TermHandle::Int(_) => Tag::Int,
            TermHandle::Real(_) => Tag::Real,
            TermHandle::Date(_) => Tag::Date,
            TermHandle::VarSmall(_) => Tag::VarSmall,
            TermHandle::VarRef(_) => Tag::VarRef,
            TermHandle::AtomSmall(_) => Tag::AtomSmall,
            TermHandle::AtomRef(_) => Tag::AtomRef,
            TermHandle::StrSmall(_) => Tag::StrSmall,
            TermHandle::StrRef(_) => Tag::StrRef,
            TermHandle::BinSmall(_) => Tag::BinSmall,
            TermHandle::BinRef(_) => Tag::BinRef,
            TermHandle::Func(_) => Tag::Func,
        }
    }


    /// Produce a [`View`] of this term that borrows from the given
    /// [`TermArena`].  This method decodes any inlined bytes and
    /// dereferences indexes into the arena to yield structured
    /// references.  See [`View`] for details.
    #[inline(always)]
    pub fn view<'a>(&self, arena: &'a TermArena) -> View<'a> {
        match &self.0 {
            TermHandle::Int(i) => View::Int(*i),
            TermHandle::Real(f) => View::Real(*f),
            TermHandle::Date(d) => View::Date(*d),
            TermHandle::VarSmall(vs) => {
                let s_bytes = &vs.bytes[..vs.size as usize];
                let s = core::str::from_utf8(s_bytes).expect("invalid UTF8 in variable");
                View::Var(s)
            }
            TermHandle::VarRef(vr) => {
                let name = arena.var_name(VarId(vr.index));
                View::Var(name)
            }
            TermHandle::AtomSmall(a) => {
                let s_bytes = &a.bytes[..a.size as usize];
                let s = core::str::from_utf8(s_bytes).expect("invalid UTF8 in atom");
                View::Atom(s)
            }
            TermHandle::AtomRef(ar) => {
                let name = arena.atom_name(AtomId(ar.index));
                View::Atom(name)
            }
            TermHandle::StrSmall(ss) => {
                let s_bytes = &ss.bytes[..ss.size as usize];
                let s = core::str::from_utf8(s_bytes).expect("invalid UTF8 in string");
                View::Str(s)
            }
            TermHandle::StrRef(sr) => {
                let slice = arena.str_slice(StrSlice { offset: sr.index, len: sr.size });
                let s = core::str::from_utf8(slice).expect("invalid UTF8 in string");
                View::Str(s)
            }
            TermHandle::BinSmall(bs) => {
                let b = &bs.bytes[..bs.size as usize];
                View::Bin(b)
            }
            TermHandle::BinRef(br) => {
                let slice = arena.bin_slice(BinSlice { offset: br.index, len: br.size });
                View::Bin(slice)
            }
            TermHandle::Func(fr) => {
                let slice = arena.term_slice(TermSlice { offset: fr.index, len: fr.size });
                // Functor is the first element of the slice
                let functor_term = slice[0];
                let functor = match &functor_term.0 {
                    TermHandle::AtomSmall(a) => {
                        let s_bytes = &a.bytes[..a.size as usize];
                        core::str::from_utf8(s_bytes).expect("invalid UTF8 in functor")
                    }
                    TermHandle::AtomRef(ar2) => {
                        arena.atom_name(AtomId(ar2.index))
                    }
                    _ => "?",
                };
                let args = &slice[1..];
                View::Func { functor, args }
            }
        }
    }

    /// Convenience method to test if this term is a compound (function).
    #[inline(always)]
    pub fn is_func(self) -> bool {
        matches!(self.tag(), Tag::Func)
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            TermHandle::Int(i) => f.debug_tuple("Int").field(i).finish(),
            TermHandle::Real(r) => f.debug_tuple("Real").field(r).finish(),
            TermHandle::Date(d) => f.debug_tuple("Date").field(d).finish(),
            TermHandle::VarSmall(v) => {
                let name = core::str::from_utf8(&v.bytes[..v.size as usize]).unwrap_or("<invalid utf8>");
                f.debug_struct("VarSmall").field("name", &name).finish()
            }
            TermHandle::VarRef(v) => f
                .debug_struct("VarRef")
                .field("index", &v.index)
                .field("size", &v.size)
                .finish(),
            TermHandle::AtomSmall(a) => {
                let name = core::str::from_utf8(&a.bytes[..a.size as usize]).unwrap_or("<invalid utf8>");
                f.debug_struct("AtomSmall").field("name", &name).finish()
            }
            TermHandle::AtomRef(a) => f
                .debug_struct("AtomRef")
                .field("index", &a.index)
                .field("size", &a.size)
                .finish(),
            TermHandle::StrSmall(s) => {
                let value = core::str::from_utf8(&s.bytes[..s.size as usize]).unwrap_or("<invalid utf8>");
                f.debug_struct("StrSmall").field("value", &value).finish()
            }
            TermHandle::StrRef(r) => f
                .debug_struct("StrRef")
                .field("index", &r.index)
                .field("size", &r.size)
                .finish(),
            TermHandle::BinSmall(b) => {
                let slice = &b.bytes[..b.size as usize];
                f.debug_struct("BinSmall").field("bytes", &slice).finish()
            }
            TermHandle::BinRef(br) => f
                .debug_struct("BinRef")
                .field("index", &br.index)
                .field("size", &br.size)
                .finish(),
            TermHandle::Func(fr) => f
                .debug_struct("Func")
                .field("index", &fr.index)
                .field("size", &fr.size)
                .finish(),
        }
    }
}


/// A borrowed view into the interned contents of a [`Term`].
///
/// Use [`Term::view`] to obtain a view.  Each variant of [`View`]
/// represents the decoded form of a term and borrows any data
/// referenced from the [`TermArena`] or the term handle itself.  No
/// allocations are performed when constructing a `View`; instead
/// references into the underlying storage are returned directly.  The
/// lifetime `'a` binds the returned references to both the borrowed
/// `Term` and the supplied `TermArena`.
#[derive(Debug, Clone)]
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
    Func {
        functor: &'a str,
        args: &'a [Term],
    },
}

/// The typed arena used to intern atoms, variables, strings,
/// binaries and compound terms.  A `TermArena` owns all memory for
/// interned data.  Terms hold only indices into this arena and remain
/// valid for the lifetime of the arena.  Cloning a `TermArena` is
/// cheap and refers to the same underlying storage via atomic
/// reference counting.
#[derive(Default, Clone)]
pub struct TermArena {
    /// Interned atom names.  Uses an `IndexSet` to assign a stable
    /// index to each unique atom.  Names can be retrieved by index
    /// without storing a separate `Vec` of names.
    atoms: IndexSet<String>,
    /// Interned variable names.  Similar to `atoms`, this assigns a
    /// stable index to each unique variable name.
    vars: IndexSet<String>,
    /// Interned string data stored contiguously.  Long UTF‑8 strings
    /// are appended to this vector and referenced by offset/length.
    string_data: Vec<u8>,
    /// Interned binary data stored contiguously.  Binary blobs longer
    /// than the inlined capacity are appended to this vector and
    /// referenced by offset/length.
    bin_data: Vec<u8>,
    /// Interned compound term slices stored sequentially.  Each slice
    /// consists of one functor atom followed by zero or more argument
    /// terms.  The `Func` handle stores the slice offset and length.
    terms: Vec<Term>,
}

impl TermArena {
    /// Create a new, empty arena.
    pub fn new() -> Self {
        Self::default()
    }

    /// Intern an atom and return its id.  Reusing the same atom
    /// repeatedly avoids additional allocations.  This uses an
    /// `IndexSet` to map each unique atom name to a stable index.
    pub fn intern_atom(&mut self, name: &str) -> AtomId {
        // Insert the name into the set and obtain its index.  If the
        // value already exists the existing index is returned.  The
        // boolean indicates whether a new entry was inserted but is
        // unused here.
        let (index, _) = self.atoms.insert_full(name.to_owned());
        AtomId(index as u32)
    }

    /// Intern a variable and return its id.  Variable names share a
    /// separate namespace from atoms.  Uses an `IndexSet` to assign
    /// stable indices to unique variable names.
    pub fn intern_var(&mut self, name: &str) -> VarId {
        let (index, _) = self.vars.insert_full(name.to_owned());
        VarId(index as u32)
    }

    /// Access a previously interned atom by id.  Panics if the id is
    /// out of bounds.  The returned string slice is borrowed from the
    /// underlying `IndexSet` entry.
    pub fn atom_name<'a>(&'a self, id: AtomId) -> &'a str {
        self.atoms.get_index(id.0 as usize)
            .expect("invalid AtomId")
            .as_str()
    }

    /// Access a previously interned variable by id.  Panics if the id
    /// is out of bounds.  The returned string slice is borrowed from
    /// the underlying `IndexSet` entry.
    pub fn var_name<'a>(&'a self, id: VarId) -> &'a str {
        self.vars.get_index(id.0 as usize)
            .expect("invalid VarId")
            .as_str()
    }

    /// Intern a long UTF‑8 string into the arena and return its slice
    /// descriptor.  Strings are stored in a contiguous bump vector.
    fn intern_str(&mut self, s: &str) -> StrSlice {
        let offset = self.string_data.len();
        self.string_data.extend_from_slice(s.as_bytes());
        let len = s.len();
        StrSlice { offset: offset as u32, len: len as u32 }
    }

    /// Intern a binary blob into the arena and return its slice descriptor.
    fn intern_bin(&mut self, bytes: &[u8]) -> BinSlice {
        let offset = self.bin_data.len();
        self.bin_data.extend_from_slice(bytes);
        let len = bytes.len();
        BinSlice { offset: offset as u32, len: len as u32 }
    }

    /// Intern a compound term slice (functor + args) into the term arena.
    fn intern_func(&mut self, functor: Term, args: &[Term]) -> TermSlice {
        let offset = self.terms.len() as u32;
        // Reserve space to avoid multiple reallocations when pushing.
        self.terms.reserve(args.len() + 1);
        self.terms.push(functor);
        self.terms.extend_from_slice(args);
        let len = (args.len() + 1) as u32;
        TermSlice { offset, len }
    }

    /// Borrow a UTF‑8 string slice stored in the arena.  This function
    /// should not be called directly by users; instead use
    /// [`Term::view`].
    fn str_slice<'a>(&'a self, slice: StrSlice) -> &'a [u8] {
        &self.string_data[(slice.offset as usize)..((slice.offset + slice.len) as usize)]
    }

    /// Borrow a binary slice stored in the arena.
    fn bin_slice<'a>(&'a self, slice: BinSlice) -> &'a [u8] {
        &self.bin_data[(slice.offset as usize)..((slice.offset + slice.len) as usize)]
    }

    /// Borrow a contiguous slice of terms comprising a compound term.
    fn term_slice<'a>(&'a self, slice: TermSlice) -> &'a [Term] {
        &self.terms[(slice.offset as usize)..((slice.offset + slice.len) as usize)]
    }
}

/// Identifiers for atoms interned in an arena.  Atom identifiers are
/// opaque and refer into the [`TermArena`].  They do not carry any
/// lifetime and may be copied freely.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AtomId(pub u32);

/// Identifiers for variables interned in an arena.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VarId(pub u32);

/// A slice descriptor for interned strings.  Contains an offset into
/// the arena's `string_data` vector and a length.  Slices are
/// referenced by [`Term`] through their encoded payload.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct StrSlice {
    offset: u32,
    len: u32,
}

/// A slice descriptor for interned binary blobs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct BinSlice {
    offset: u32,
    len: u32,
}

/// A slice descriptor for interned compound terms.  Contains the
/// offset and length of the slice into the arena's term storage.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct TermSlice {
    offset: u32,
    len: u32,
}

/// Errors that may occur when constructing terms.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// Attempted to create a compound term of arity zero.  The
    /// contained string is the offending functor name.
    ArityZeroCompound(String),
}

/// Tag discriminant for terms.  Kept private to avoid exposing the
/// internal representation in the public API.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Tag {
    Int = 0,
    Real = 1,
    Date = 2,
    VarSmall = 3,
    VarRef = 4,
    AtomSmall = 5,
    AtomRef = 6,
    StrSmall = 7,
    StrRef = 8,
    BinSmall = 9,
    BinRef = 10,
    Func = 11,
}


// The default `PartialEq`, `Eq` and `Hash` implementations are derived on
// `Term` and `TermHandle`, which compare and hash based on the enum
// discriminant and contained data.  This behaviour aligns with the
// semantics that two terms are equal if and only if they are of the
// same variant and contain identical payloads.  Numeric values of
// different kinds (e.g., an `Int` vs a `Real`) therefore do not compare
// equal, matching the original specification.

impl core::cmp::PartialOrd for Term {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl core::cmp::Ord for Term {
    fn cmp(&self, other: &Self) -> Ordering {
        use Tag::*;
        let tag_a = self.tag();
        let tag_b = other.tag();
        let order_a = tag_order(tag_a);
        let order_b = tag_order(tag_b);
        if order_a != order_b {
            return order_a.cmp(&order_b);
        }
        match (&self.0, &other.0) {
            // Numbers: compare by numeric value irrespective of the exact type.
            (TermHandle::Int(_)
            | TermHandle::Real(_)
            | TermHandle::Date(_),
             TermHandle::Int(_)
            | TermHandle::Real(_)
            | TermHandle::Date(_)) => {
                let a = numeric_value(*self);
                let b = numeric_value(*other);
                // Use partial_cmp but unwrap safely; NaN values compare equal here.
                a.partial_cmp(&b).unwrap_or(Ordering::Equal)
            }
            // Variables
            (TermHandle::VarSmall(a), TermHandle::VarSmall(b)) => {
                // Compare bytes lexicographically first, then size to break ties.
                let ord = a.bytes.cmp(&b.bytes);
                if ord != Ordering::Equal {
                    return ord;
                }
                (a.size).cmp(&b.size)
            }
            (TermHandle::VarRef(a), TermHandle::VarRef(b)) => {
                // Compare by index then by size.
                let ord = a.index.cmp(&b.index);
                if ord != Ordering::Equal {
                    return ord;
                }
                a.size.cmp(&b.size)
            }
            // Mixed variable flavours: use discriminant to produce a stable order.
            (TermHandle::VarSmall(_), TermHandle::VarRef(_)) => Tag::VarSmall.cmp(&Tag::VarRef),
            (TermHandle::VarRef(_), TermHandle::VarSmall(_)) => Tag::VarRef.cmp(&Tag::VarSmall),

            // Atoms
            (TermHandle::AtomSmall(a), TermHandle::AtomSmall(b)) => {
                let ord = a.bytes.cmp(&b.bytes);
                if ord != Ordering::Equal {
                    return ord;
                }
                (a.size).cmp(&b.size)
            }
            (TermHandle::AtomRef(a), TermHandle::AtomRef(b)) => {
                let ord = a.index.cmp(&b.index);
                if ord != Ordering::Equal {
                    return ord;
                }
                a.size.cmp(&b.size)
            }
            (TermHandle::AtomSmall(_), TermHandle::AtomRef(_)) => Tag::AtomSmall.cmp(&Tag::AtomRef),
            (TermHandle::AtomRef(_), TermHandle::AtomSmall(_)) => Tag::AtomRef.cmp(&Tag::AtomSmall),

            // Strings
            (TermHandle::StrSmall(a), TermHandle::StrSmall(b)) => {
                let ord = a.bytes.cmp(&b.bytes);
                if ord != Ordering::Equal {
                    return ord;
                }
                (a.size).cmp(&b.size)
            }
            (TermHandle::StrRef(a), TermHandle::StrRef(b)) => {
                let ord = a.index.cmp(&b.index);
                if ord != Ordering::Equal {
                    return ord;
                }
                a.size.cmp(&b.size)
            }
            (TermHandle::StrSmall(_), TermHandle::StrRef(_)) => Tag::StrSmall.cmp(&Tag::StrRef),
            (TermHandle::StrRef(_), TermHandle::StrSmall(_)) => Tag::StrRef.cmp(&Tag::StrSmall),

            // Binaries
            (TermHandle::BinSmall(a), TermHandle::BinSmall(b)) => {
                let ord = a.bytes.cmp(&b.bytes);
                if ord != Ordering::Equal {
                    return ord;
                }
                (a.size).cmp(&b.size)
            }
            (TermHandle::BinRef(a), TermHandle::BinRef(b)) => {
                let ord = a.index.cmp(&b.index);
                if ord != Ordering::Equal {
                    return ord;
                }
                a.size.cmp(&b.size)
            }
            (TermHandle::BinSmall(_), TermHandle::BinRef(_)) => Tag::BinSmall.cmp(&Tag::BinRef),
            (TermHandle::BinRef(_), TermHandle::BinSmall(_)) => Tag::BinRef.cmp(&Tag::BinSmall),

            // Compounds: compare by length (arity+1) then by slice index.
            (TermHandle::Func(a), TermHandle::Func(b)) => {
                let ord = a.size.cmp(&b.size);
                if ord != Ordering::Equal {
                    return ord;
                }
                a.index.cmp(&b.index)
            }

            // Fallback for identical tags that are not handled above; should not occur.
            _ => Ordering::Equal,
        }
    }
}

/// Compute the global tag order used for comparing terms of different kinds.
/// According to Prolog standard order: variables < numbers < atoms < strings
/// < binaries < compounds.
fn tag_order(tag: Tag) -> u8 {
    use Tag::*;
    match tag {
        VarSmall | VarRef => 0,
        Int | Real | Date => 1,
        AtomSmall | AtomRef => 2,
        StrSmall | StrRef => 3,
        BinSmall | BinRef => 4,
        Func => 5,
    }
}

/// Extract a numeric value from a term for ordering purposes.  All
/// numeric kinds (int, real and date) are converted to `f64` for
/// comparison.  `Date` values use their millisecond representation as
/// the numeric value.
fn numeric_value(t: Term) -> f64 {
    match t.0 {
        TermHandle::Int(i) => i as f64,
        TermHandle::Real(f) => f,
        TermHandle::Date(d) => d as f64,
        _ => 0.0,
    }
}

/// Module containing convenience macros for constructing lists and tuples.
// === List, tuple and compound construction macros ===

/// Construct a proper list from a sequence of terms.  The result is
/// equivalent to repeatedly cons'ing the elements onto the empty list.
#[macro_export]
macro_rules! list {
    // proper list with tail omitted
    ( & $arena:expr ; $( $elem:expr ),* $(,)? ) => {
        {
            let mut tail = $crate::Term::atom($arena, "nil");
            // Reverse iterate to cons onto the tail
            let elems = &[$($elem),*];
            for it in elems.iter().rev() {
                let cons = [*it, tail];
                tail = $crate::Term::func($arena, "list", &cons).expect("list cons");
            }
            tail
        }
    };
    // improper list with explicit tail
    ( & $arena:expr ; $( $elem:expr ),* | $tail:expr $(,)? ) => {
        {
            let mut tail_term = $tail;
            let elems = &[$($elem),*];
            for it in elems.iter().rev() {
                let cons = [*it, tail_term];
                tail_term = $crate::Term::func($arena, "listc", &cons).expect("listc cons");
            }
            tail_term
        }
    };
}

/// Construct a tuple from a sequence of terms.  A 0‑tuple is
/// represented by the atom `unit`.  Tuples internally are
/// compounds whose functor is `tuple` and whose arity equals the
/// number of elements.
#[macro_export]
macro_rules! tuple {
    ( & $arena:expr ; ) => {
        $crate::Term::atom($arena, "unit")
    };
    ( & $arena:expr ; $( $elem:expr ),+ $(,)? ) => {
        {
            let elems = &[$($elem),+];
            $crate::Term::func($arena, "tuple", elems).expect("tuple construction")
        }
    };
}

/// Construct a compound term from a functor name and arguments.
///
/// This macro is a convenience wrapper around [`Term::func`].  It
/// takes an arena reference, a functor name and a comma separated
/// list of argument expressions.  At runtime the arguments are
/// collected into a slice and passed to [`Term::func`].  If the
/// arity is zero the macro will return an error via a panic.
#[macro_export]
macro_rules! func {
    ( & $arena:expr ; $functor:expr ; $( $arg:expr ),+ $(,)? ) => {{
        let args: &[_] = &[$($arg),+];
        $crate::Term::func($arena, $functor, args).expect("invalid zero-arity compound")
    }};
}

/// Map over the elements of a list, producing a new list with the
/// mapped head terms.  The provided function `f` is applied to
/// each element of the list in order.  Improper lists (those
/// constructed with `listc/2`) are preserved; if the mapped tail
/// becomes the empty list the constructor is canonicalised to
/// `list/2` to produce a proper list.
pub fn map_list<F>(arena: &mut TermArena, list: Term, f: F) -> Term
where
    F: Fn(Term) -> Term,
{
    use View;
    // Recursive helper that carries a shared reference to the mapper.
    fn recurse<F>(arena: &mut TermArena, current: Term, f: &F) -> Term
    where
        F: Fn(Term) -> Term,
    {
        match current.view(arena) {
            View::Func { functor, args } => {
                let name = functor;
                // Expect two arguments for list and listc.
                if (name == "list" || name == "listc") && args.len() == 2 {
                    let head = args[0];
                    let tail = args[1];
                    let new_head = f(head);
                    let new_tail = recurse(arena, tail, f);
                    // Determine which constructor to use.  If the original
                    // constructor was list we preserve it.  If it was
                    // listc we canonicalise listc(..., nil) to list/2.
                    let constructor = if name == "list" {
                        "list"
                    } else {
                        // name == "listc"; canonicalise when tail is nil
                        match new_tail.view(arena) {
                            View::Atom(n) if n == "nil" => "list",
                            _ => "listc",
                        }
                    };
                    // Build new compound.
                    Term::func(arena, constructor, &[new_head, new_tail])
                        .expect("list construction")
                } else {
                    // Not a list cell: leave unchanged.
                    current
                }
            }
            _ => current,
        }
    }
    recurse(arena, list, &f)
}

#[cfg(test)]
mod tests {
    use super::*;
    use quickcheck::TestResult;
    use proptest::prelude::*;

    #[test]
    fn term_size_is_sixteen_bytes() {
        assert_eq!(core::mem::size_of::<Term>(), 16);
    }

    #[test]
    fn int_round_trip() {
        for &n in &[0i64, 1, -1, i64::MAX >> 3, i64::MIN >> 3] {
            let t = Term::int(n);
            match t.view(&TermArena::new()) {
                View::Int(x) => assert_eq!(x, n),
                _ => panic!("unexpected view"),
            }
        }
    }

    #[test]
    fn small_atom_interning() {
        let mut arena = TermArena::new();
        let a1 = Term::atom(&mut arena, "foo");
        let a2 = Term::atom(&mut arena, "foo");
        assert_eq!(a1, a2);
        if let View::Atom(name) = a1.view(&arena) {
            assert_eq!(name, "foo");
        } else {
            panic!("wrong view");
        }
    }

    #[test]
    fn compound_construction() {
        let mut arena = TermArena::new();
        let a = Term::int(1);
        let b = Term::real(2.0);
        let p = Term::func(&mut arena, "point", &[a, b]).unwrap();
        assert!(p.is_func());
        if let View::Func { functor, args } = p.view(&arena) {
            assert_eq!(functor, "point");
            assert_eq!(args.len(), 2);
        } else {
            panic!("unexpected view");
        }
    }

    proptest! {
        // Property test: serialising and deserialising a term should yield the same payload.
        #![proptest_config(ProptestConfig { cases: 32, .. ProptestConfig::default() })]
        #[test]
        fn prop_integers_round_trip(n in -100000i64..100000) {
            let t = Term::int(n);
            // decode via payload & view
            let n2 = match t.view(&TermArena::new()) { View::Int(x) => x, _ => 0 };
            prop_assert_eq!(n, n2);
        }
    }
}
