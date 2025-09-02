//! A lightweight, arena‑backed representation of Prolog–like terms.
//!
//! This crate provides a compact [`Term`] type for representing Prolog-like
//! data structures, along with a typed arena [`TermArena`] used to
//! intern atoms, variables, strings, binaries and compound terms.  The
//! underlying representation is designed around a fixed‐width 16
//! byte handle which carries both the tag and value of a term.
//!
//! The primary entry points are [`TermArena`] (for allocating
//! interned data) and [`Term`] (the user visible term handle).  Terms
//! can be matched using the [`Term::view`] method which yields a
//! [`TermView`] that borrows from the underlying arena.  Equality and
//! ordering are well defined according to Prolog's standard order of
//! terms.  Users may construct lists and tuples conveniently via
//! macros exported from this crate.

//#[cfg(feature = "no_std")]
//use alloc::{string::String, vec::Vec};
//#[cfg(feature = "no_std")]
//use core::cmp::Ordering;

use core::fmt;

//#[cfg(not(feature = "no_std"))]
use std::cmp::Ordering;

use indexmap::IndexSet;

// The following type definitions describe the internal representation
// of a term.  Rather than packing data into a single integer we use
// a tagged enum to store the various kinds of terms.  Each variant
// carries its associated data directly, for example a 64 bit integer
// for numeric types or a small inline buffer for short atoms and
// variables.  Long names or sequences store an index and size into
// the appropriate arena.

#[derive(Copy, Clone, PartialEq)]
struct Small {
    bytes: [u8; 14],
    size: u8,
}

#[derive(Copy, Clone, PartialEq)]
struct Index {
    arena_id: u32,
    index: u32,
}

#[derive(Copy, Clone, PartialEq)]
struct Slice {
    arena_id: u32,
    index: u32,
    size: u32,
}

/// Internal handle describing the kind of a term and storing its data.
///
/// Each variant stores the associated value directly.  The `repr(u8)`
/// attribute ensures the discriminant occupies a single byte, which
/// together with the payloads yields a `Term` size of 16 bytes on
/// 64‑bit targets.
#[repr(u8)]
#[derive(Copy, Clone, PartialEq)]
enum TermHandle {
    Int(i64),
    Real(f64),
    Date(i64),
    VarSmall(Small),
    VarRef(Index),
    AtomSmall(Small),
    AtomRef(Index),
    StrSmall(Small),
    StrRef(Slice),
    BinSmall(Small),
    BinRef(Slice),
    FuncRef(Slice),
}

/// A compact, copyable handle referencing a term stored in a [`TermArena`].
///
/// Internally a `Term` stores a single [`TermHandle`] enum variant.
/// On 64‑bit targets the discriminant and associated payload occupy
/// 16 bytes in total.  Users should never construct `Term` values
/// directly; instead use the associated constructors or the
/// convenience macros in the [`term`] module.
/// Instances of `Term` are cheap to copy (`Copy` and `Clone`).
#[derive(Copy, Clone, PartialEq)]
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
            Term(TermHandle::AtomSmall(Small {
                bytes: buf,
                size: bytes.len() as u8,
            }))
        } else {
            let id = arena.intern_atom(name);
            Term(TermHandle::AtomRef(Index {
                arena_id: arena.id,
                index: id.0,
            }))
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
            Term(TermHandle::VarSmall(Small {
                bytes: buf,
                size: bytes.len() as u8,
            }))
        } else {
            let id = arena.intern_var(name);
            Term(TermHandle::VarRef(Index {
                arena_id: arena.id,
                index: id.0,
            }))
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
            Term(TermHandle::StrSmall(Small {
                bytes: buf,
                size: bytes.len() as u8,
            }))
        } else {
            let slice = arena.intern_str(s);
            Term(TermHandle::StrRef(Slice {
                arena_id: arena.id,
                index: slice.offset,
                size: slice.len,
            }))
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
            Term(TermHandle::BinSmall(Small {
                bytes: buf,
                size: bytes.len() as u8,
            }))
        } else {
            let slice = arena.intern_bin(bytes);
            Term(TermHandle::BinRef(Slice {
                arena_id: arena.id,
                index: slice.offset,
                size: slice.len,
            }))
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
        Ok(Term(TermHandle::FuncRef(Slice {
            arena_id: arena.id,
            index: slice.offset,
            size: slice.len,
        })))
    }

    /// Constant representing the zero‑arity tuple (unit).  Internally
    /// this is the atom `"unit"` encoded as a small atom.  It may
    /// be copied freely and does not depend on any arena.
    pub const UNIT: Self = {
        let buf: [u8; 14] = [b'u', b'n', b'i', b't', 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
        Term(TermHandle::AtomSmall(Small {
            bytes: buf,
            size: 4,
        }))
    };

    /// Constant representing the empty list (nil).  Internally this is
    /// the atom `"nil"` encoded as a small atom.  It may be copied
    /// freely and does not depend on any arena.
    pub const NIL: Self = {
        let buf: [u8; 14] = [b'n', b'i', b'l', 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
        Term(TermHandle::AtomSmall(Small {
            bytes: buf,
            size: 3,
        }))
    };

    /// Produce a [`TermView`] of this term that borrows from the given
    /// [`TermArena`].  This method decodes any inlined bytes and
    /// dereferences indexes into the arena to yield structured
    /// references.  See [`TermView`] for details.
    #[inline(always)]
    pub fn view<'a>(&'a self, arena: &'a TermArena) -> TermView<'a> {
        match &self.0 {
            TermHandle::Int(i) => TermView::Int(*i),
            TermHandle::Real(f) => TermView::Real(*f),
            TermHandle::Date(d) => TermView::Date(*d),
            TermHandle::VarSmall(vs) => {
                let s_bytes = &vs.bytes[..vs.size as usize];
                let s = core::str::from_utf8(s_bytes).expect("invalid UTF8 in variable");
                TermView::Var(s)
            }
            TermHandle::VarRef(vr) => {
                let name = arena.var_name(VarId(vr.index));
                TermView::Var(name)
            }
            TermHandle::AtomSmall(a) => {
                let s_bytes = &a.bytes[..a.size as usize];
                let s = core::str::from_utf8(s_bytes).expect("invalid UTF8 in atom");
                TermView::Atom(s)
            }
            TermHandle::AtomRef(ar) => {
                let name = arena.atom_name(AtomId(ar.index));
                TermView::Atom(name)
            }
            TermHandle::StrSmall(ss) => {
                let s_bytes = &ss.bytes[..ss.size as usize];
                let s = core::str::from_utf8(s_bytes).expect("invalid UTF8 in string");
                TermView::Str(s)
            }
            TermHandle::StrRef(sr) => {
                let slice = arena.str_slice(StrSlice {
                    offset: sr.index,
                    len: sr.size,
                });
                let s = core::str::from_utf8(slice).expect("invalid UTF8 in string");
                TermView::Str(s)
            }
            TermHandle::BinSmall(bs) => {
                let b = &bs.bytes[..bs.size as usize];
                TermView::Bin(b)
            }
            TermHandle::BinRef(br) => {
                let slice = arena.bin_slice(BinSlice {
                    offset: br.index,
                    len: br.size,
                });
                TermView::Bin(slice)
            }
            TermHandle::FuncRef(fr) => {
                let slice = arena.term_slice(TermSlice {
                    offset: fr.index,
                    len: fr.size,
                });
                // Functor is the first element of the slice
                let functor = match &slice[0].0 {
                    TermHandle::AtomSmall(a) => {
                        let s_bytes = &a.bytes[..a.size as usize];
                        core::str::from_utf8(s_bytes).expect("invalid UTF8 in functor")
                    }
                    TermHandle::AtomRef(ar2) => arena.atom_name(AtomId(ar2.index)),
                    _ => panic!("invalid functor"),
                };
                let args = &slice[1..];
                TermView::Func(arena, functor, args)
            }
        }
    }

    #[inline(always)]
    pub fn is_func(&self) -> bool {
        matches!(self.0, TermHandle::FuncRef(_))
    }

    #[inline(always)]
    pub fn is_atom(&self) -> bool {
        matches!(self.0, TermHandle::AtomSmall(_) | TermHandle::AtomRef(_))
    }

    #[inline(always)]
    pub fn arity(&self) -> usize {
        match &self.0 {
            TermHandle::FuncRef(Slice { size: n, .. }) => (n - 1) as usize,
            _ => 0,
        }
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            TermHandle::Int(i) => f.debug_tuple("Int").field(i).finish(),
            TermHandle::Real(r) => f.debug_tuple("Real").field(r).finish(),
            TermHandle::Date(d) => f.debug_tuple("Date").field(d).finish(),
            TermHandle::VarSmall(v) => {
                let name =
                    core::str::from_utf8(&v.bytes[..v.size as usize]).unwrap_or("<invalid utf8>");
                f.debug_struct("VarSmall").field("name", &name).finish()
            }
            TermHandle::VarRef(v) => f.debug_struct("VarRef").field("index", &v.index).finish(),
            TermHandle::AtomSmall(a) => {
                let name =
                    core::str::from_utf8(&a.bytes[..a.size as usize]).unwrap_or("<invalid utf8>");
                f.debug_struct("AtomSmall").field("name", &name).finish()
            }
            TermHandle::AtomRef(a) => f.debug_struct("AtomRef").field("index", &a.index).finish(),
            TermHandle::StrSmall(s) => {
                let value =
                    core::str::from_utf8(&s.bytes[..s.size as usize]).unwrap_or("<invalid utf8>");
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
            TermHandle::FuncRef(fr) => f
                .debug_struct("Func")
                .field("index", &fr.index)
                .field("size", &fr.size)
                .finish(),
        }
    }
}

impl fmt::Debug for TermView<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            TermView::Int(i) => f.debug_tuple("Int").field(&i).finish(),
            TermView::Real(r) => f.debug_tuple("Real").field(&r).finish(),
            TermView::Date(d) => f.debug_tuple("Date").field(&d).finish(),
            TermView::Var(v) => f.debug_tuple("Var").field(&v).finish(),
            TermView::Atom(a) => f.debug_tuple("Atom").field(&a).finish(),
            TermView::Str(s) => f.debug_tuple("Str").field(&s).finish(),
            TermView::Bin(b) => f.debug_tuple("Bin").field(&b).finish(),
            TermView::Func(a, fr, ts) => f
                .debug_tuple("Func")
                .field(&a.id)
                .field(&fr)
                .field(&ts.iter().map(|t| t.view(a)).collect::<Vec<_>>())
                .finish(),
        }
    }
}

/// A borrowed view into the interned contents of a [`Term`].
///
/// Use [`Term::view`] to obtain a view.  Each variant of [`TermView`]
/// represents the decoded form of a term and borrows any data
/// referenced from the [`TermArena`] or the term handle itself.  No
/// allocations are performed when constructing a `TermView`; instead
/// references into the underlying storage are returned directly.  The
/// lifetime `'a` binds the returned references to both the borrowed
/// `Term` and the supplied `TermArena`.
#[derive(Clone, Copy)]
pub enum TermView<'a> {
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
    Func(&'a TermArena, &'a str, &'a [Term]),
}

/// The typed arena used to intern atoms, variables, strings,
/// binaries and compound terms.  A `TermArena` owns all memory for
/// interned data.  Terms hold only indices into this arena and remain
/// valid for the lifetime of the arena.
#[derive(Default, Clone, Debug)]
pub struct TermArena {
    /// Randomly generated arena identifier.
    /// Terms referencing an arena include this ID, which is later used to verify  
    /// that they correspond to the correct arena when the term value is retrieved.
    id: u32,
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
        Self {
            id: rand::random(),
            ..Self::default()
        }
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
        self.atoms
            .get_index(id.0 as usize)
            .expect("invalid AtomId")
            .as_str()
    }

    /// Access a previously interned variable by id.  Panics if the id
    /// is out of bounds.  The returned string slice is borrowed from
    /// the underlying `IndexSet` entry.
    pub fn var_name<'a>(&'a self, id: VarId) -> &'a str {
        self.vars
            .get_index(id.0 as usize)
            .expect("invalid VarId")
            .as_str()
    }

    /// Intern a long UTF‑8 string into the arena and return its slice
    /// descriptor.  Strings are stored in a contiguous bump vector.
    fn intern_str(&mut self, s: &str) -> StrSlice {
        let offset = self.string_data.len();
        self.string_data.extend_from_slice(s.as_bytes());
        let len = s.len();
        StrSlice {
            offset: offset as u32,
            len: len as u32,
        }
    }

    /// Intern a binary blob into the arena and return its slice descriptor.
    fn intern_bin(&mut self, bytes: &[u8]) -> BinSlice {
        let offset = self.bin_data.len();
        self.bin_data.extend_from_slice(bytes);
        let len = bytes.len();
        BinSlice {
            offset: offset as u32,
            len: len as u32,
        }
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
#[derive(Debug, Clone, Copy)]
pub struct AtomId(pub u32);

/// Identifiers for variables interned in an arena.
#[derive(Debug, Clone, Copy)]
pub struct VarId(pub u32);

/// A slice descriptor for interned strings.  Contains an offset into
/// the arena's `string_data` vector and a length.  Slices are
/// referenced by [`Term`] through their encoded payload.
#[derive(Debug, Clone, Copy)]
struct StrSlice {
    offset: u32,
    len: u32,
}

/// A slice descriptor for interned binary blobs.
#[derive(Debug, Clone, Copy)]
struct BinSlice {
    offset: u32,
    len: u32,
}

/// A slice descriptor for interned compound terms.  Contains the
/// offset and length of the slice into the arena's term storage.
#[derive(Debug, Clone, Copy)]
struct TermSlice {
    offset: u32,
    len: u32,
}

/// Errors that may occur when constructing terms.
#[derive(Debug, Clone)]
pub enum Error {
    /// Attempted to create a compound term of arity zero.  The
    /// contained string is the offending functor name.
    ArityZeroCompound(String),
}

impl<'a> PartialEq for TermView<'a> {
    fn eq(&self, other: &Self) -> bool {
        let order_a = kind_order(self);
        let order_b = kind_order(other);
        if order_a != order_b {
            return false;
        }
        match (self, other) {
            // Numbers: compare by numeric value irrespective of the exact type.
            (
                TermView::Int(_) | TermView::Real(_) | TermView::Date(_),
                TermView::Int(_) | TermView::Real(_) | TermView::Date(_),
            ) => {
                let a = numeric_value(self);
                let b = numeric_value(other);
                a == b
            }
            // Variables
            (TermView::Var(a), TermView::Var(b)) => a == b,
            // Atoms
            (TermView::Atom(a), TermView::Atom(b)) => a == b,
            // Strings
            (TermView::Str(a), TermView::Str(b)) => a == b,
            // Binaries
            (TermView::Bin(a), TermView::Bin(b)) => a == b,
            // Compounds: compare by length (arity+1) then by slice index.
            (
                TermView::Func(arena_a, functor_a, args_a),
                TermView::Func(arena_b, functor_b, args_b),
            ) => {
                if args_a.len() != args_b.len() {
                    return false;
                }
                if functor_a != functor_b {
                    return false;
                }
                args_a
                    .iter()
                    .zip(args_b.iter())
                    .all(|(a, b)| a.view(arena_a) == b.view(arena_b))
            }
            _ => unreachable!(),
        }
    }
}

impl<'a> Eq for TermView<'a> {}

impl core::cmp::PartialOrd for TermView<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl core::cmp::Ord for TermView<'_> {
    fn cmp(&self, other: &Self) -> Ordering {
        let order_a = kind_order(self);
        let order_b = kind_order(other);
        if order_a != order_b {
            return order_a.cmp(&order_b);
        }
        match (self, other) {
            // Numbers: compare by numeric value irrespective of the exact type.
            (
                TermView::Int(_) | TermView::Real(_) | TermView::Date(_),
                TermView::Int(_) | TermView::Real(_) | TermView::Date(_),
            ) => {
                let a = numeric_value(self);
                let b = numeric_value(other);
                a.total_cmp(&b)
            }
            // Variables
            (TermView::Var(a), TermView::Var(b)) => a.cmp(b),
            // Atoms
            (TermView::Atom(a), TermView::Atom(b)) => a.cmp(b),
            // Strings
            (TermView::Str(a), TermView::Str(b)) => a.cmp(b),
            // Binaries
            (TermView::Bin(a), TermView::Bin(b)) => a.cmp(b),
            // Compounds: compare by length (arity+1) then by slice index.
            (
                TermView::Func(arena_a, functor_a, args_a),
                TermView::Func(arena_b, functor_b, args_b),
            ) => {
                let ord = args_a.len().cmp(&args_b.len());
                if ord != Ordering::Equal {
                    return ord;
                }
                let ord = functor_a.cmp(functor_b);
                if ord != Ordering::Equal {
                    return ord;
                }
                for (arg_a, arg_b) in args_a
                    .iter()
                    .zip(args_b.iter())
                    .map(|(a, b)| (a.view(arena_a), b.view(arena_b)))
                {
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
fn kind_order(t: &TermView) -> u8 {
    match t {
        TermView::Var(_) => 0,
        TermView::Int(_) | TermView::Real(_) | TermView::Date(_) => 1,
        TermView::Atom(_) => 2,
        TermView::Str(_) => 3,
        TermView::Bin(_) => 4,
        TermView::Func(_, _, _) => 5,
    }
}

/// Extract a numeric value from a term for ordering purposes.  All
/// numeric kinds (int, real and date) are converted to `f64` for
/// comparison.  `Date` values use their millisecond representation as
/// the numeric value.
fn numeric_value(t: &TermView) -> f64 {
    match t {
        TermView::Int(i) => *i as f64,
        TermView::Real(f) => *f,
        TermView::Date(d) => *d as f64,
        _ => unreachable!(),
    }
}

/// Module containing convenience macros for constructing lists and tuples.
// === List, tuple and compound construction macros ===

/// Construct a list from a sequence of terms.
#[macro_export]
macro_rules! list {
    // empty list
    () => {
        $crate::Term::NIL
    };
    // proper list with tail omitted
    ( &mut $arena:expr ; $( $elem:expr ),+ $(,)? ) => {
        {
            let elems = &[$($elem),+];
            $crate::Term::func(&mut $arena, "list", elems)
        }
    };
    // improper list with explicit tail
    ( &mut $arena:expr ; $( $elem:expr ),+ ; $tail:expr $(,)? ) => {
        {
            let elems = &[$($elem),+, $tail];
            $crate::Term::func(&mut $arena, "listc", elems)
        }
    };
}

/// Construct a tuple from a sequence of terms.  A 0‑tuple is
/// represented by the atom `unit`.  Tuples internally are
/// compounds whose functor is `tuple` and whose arity equals the
/// number of elements.
#[macro_export]
macro_rules! tuple {
    () => {
        $crate::Term::UNIT
    };
    ( &mut $arena:expr ; $( $elem:expr ),+ $(,)? ) => {
        {
            let elems = &[$($elem),+];
            $crate::Term::func(&mut $arena, "tuple", elems)
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
    ( &mut $arena:expr ; $functor:expr ; $( $arg:expr ),+ $(,)? ) => {{
        let args: &[_] = &[$($arg),+];
        $crate::Term::func(&mut $arena, $functor, args)
    }};
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn term_size_is_sixteen_bytes() {
        assert_eq!(core::mem::size_of::<Term>(), 16);
    }

    #[test]
    fn small_atom_interning() {
        let mut arena = TermArena::new();
        let a1 = Term::atom(&mut arena, "foo");
        let a2 = Term::atom(&mut arena, "foo");
        assert_eq!(a1, a2);
        if let TermView::Atom(name) = a1.view(&arena) {
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
        let c = Term::date(1000);
        let d = Term::atom(&mut arena, "hello");
        let e = Term::var(&mut arena, "Hello, hello, world!");
        let f = Term::str(&mut arena, "A str\ning.");
        let g = list![&mut arena; d, e, f].unwrap();
        let h = tuple![&mut arena; f].unwrap();
        let p = Term::func(&mut arena, "point", &[a, b, c, d, e, f, g, h]).unwrap();
        let p = func![&mut arena; "foo"; Term::NIL, Term::UNIT, p, p, list![], list![&mut arena; a, b; c].unwrap()].unwrap();
        dbg!(&p);
        dbg!(p.view(&arena));
        assert!(p.is_func());
        if let TermView::Func(_, functor, args) = p.view(&arena) {
            assert_eq!(functor, "foo");
            assert_eq!(p.arity(), 6);
            assert_eq!(args.len(), 6);
        } else {
            panic!("unexpected view");
        }
    }
}
