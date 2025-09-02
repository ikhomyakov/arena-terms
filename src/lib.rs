//! A lightweight, arena‑backed representation of Prolog–like terms.
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

use core::fmt;
use indexmap::IndexSet;
use smartstring::alias::String;
use std::cmp::Ordering;

// The following type definitions describe the internal representation
// of a term.  Rather than packing data into a single integer we use
// a tagged enum to store the various kinds of terms.  Each variant
// carries its associated data directly, for example a 64 bit integer
// for numeric types or a small inline buffer for short atoms and
// variables.  Long names or sequences store an index and length into
// the appropriate arena.

#[derive(Copy, Clone, PartialEq)]
struct TinyArray {
    bytes: [u8; 14],
    len: u8,
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
    VarRef(Index),
    Atom(TinyArray),
    AtomRef(Index),
    Str(TinyArray),
    StrRef(Slice),
    Bin(TinyArray),
    BinRef(Slice),
    FuncRef(Slice),
}

/// A compact, copyable handle referencing a term stored in a [`Arena`].
///
/// Internally a `Term` stores a single [`Handle`] enum variant.
/// On 64‑bit targets the discriminant and associated payload occupy
/// 16 bytes in total.  Users should never construct `Term` values
/// directly; instead use the associated constructors or the
/// convenience macros in the [`term`] module.
/// Instances of `Term` are cheap to copy (`Copy` and `Clone`).
#[derive(Copy, Clone, PartialEq)]
pub struct Term(Handle);

impl Term {
    /// Construct a new integer term.  The full 64 bit two's complement
    /// representation of `i` is stored in the payload.  No truncation
    /// occurs.
    #[inline(always)]
    pub fn int(i: i64) -> Self {
        Term(Handle::Int(i))
    }

    /// Construct a new floating point term.  The full 64 bit IEEE‑754
    /// bit pattern is stored in the payload without truncation.
    #[inline(always)]
    pub fn real(f: f64) -> Self {
        Term(Handle::Real(f))
    }

    /// Construct a new date term representing a Unix epoch in
    /// milliseconds.  Dates share the same underlying storage as
    /// integers but use a distinct tag so they do not compare equal
    /// with integer terms.
    #[inline(always)]
    pub fn date(ms: i64) -> Self {
        Term(Handle::Date(ms))
    }

    /// Construct or intern an atom into the arena and produce a term
    /// referencing it.  Small atom names (≤14 bytes of UTF‑8) are
    /// inlined directly into the handle; longer names are interned
    /// into the arena and referenced by index and length.
    #[inline(always)]
    pub fn atom(arena: &mut Arena, name: &str) -> Self {
        let bytes = name.as_bytes();
        if bytes.len() <= 14 {
            let mut buf = [0u8; 14];
            buf[..bytes.len()].copy_from_slice(bytes);
            Term(Handle::Atom(TinyArray {
                bytes: buf,
                len: bytes.len() as u8,
            }))
        } else {
            let id = arena.intern_atom(name);
            Term(Handle::AtomRef(Index {
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
    pub fn var(arena: &mut Arena, name: &str) -> Self {
        let bytes = name.as_bytes();
        if bytes.len() <= 14 {
            let mut buf = [0u8; 14];
            buf[..bytes.len()].copy_from_slice(bytes);
            Term(Handle::Var(TinyArray {
                bytes: buf,
                len: bytes.len() as u8,
            }))
        } else {
            let id = arena.intern_var(name);
            Term(Handle::VarRef(Index {
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
    pub fn str(arena: &mut Arena, s: &str) -> Self {
        let bytes = s.as_bytes();
        if bytes.len() <= 14 {
            let mut buf = [0u8; 14];
            buf[..bytes.len()].copy_from_slice(bytes);
            Term(Handle::Str(TinyArray {
                bytes: buf,
                len: bytes.len() as u8,
            }))
        } else {
            let slice = arena.intern_str(s);
            Term(Handle::StrRef(Slice {
                arena_id: arena.id,
                index: slice.index,
                len: slice.len,
            }))
        }
    }

    /// Construct or intern a binary blob into the arena and produce a
    /// term referencing it.  Blobs longer than 14 bytes are interned
    /// in the arena; shorter blobs are inlined.
    #[inline(always)]
    pub fn bin(arena: &mut Arena, bytes: &[u8]) -> Self {
        if bytes.len() <= 14 {
            let mut buf = [0u8; 14];
            buf[..bytes.len()].copy_from_slice(bytes);
            Term(Handle::Bin(TinyArray {
                bytes: buf,
                len: bytes.len() as u8,
            }))
        } else {
            let slice = arena.intern_bin(bytes);
            Term(Handle::BinRef(Slice {
                arena_id: arena.id,
                index: slice.index,
                len: slice.len,
            }))
        }
    }

    /// Construct a new compound term by interning the functor and
    /// arguments in the arena.  The returned term references a slice
    /// in the arena's term storage consisting of the functor atom as
    /// the first entry followed by the argument handles.  A functor of
    /// arity zero results in an atom.
    #[inline(always)]
    pub fn func(arena: &mut Arena, functor: &str, args: &[Term]) -> Self {
        let functor_atom = Term::atom(arena, functor);
        if args.is_empty() {
            return functor_atom;
        }
        let slice = arena.intern_func(functor_atom, args);
        Term(Handle::FuncRef(Slice {
            arena_id: arena.id,
            index: slice.index,
            len: slice.len,
        }))
    }

    /// Constant representing the zero‑arity tuple (unit).  Internally
    /// this is the atom `"unit"` encoded as a small atom.  It may
    /// be copied freely and does not depend on any arena.
    pub const UNIT: Self = {
        let buf: [u8; 14] = [b'u', b'n', b'i', b't', 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
        Term(Handle::Atom(TinyArray { bytes: buf, len: 4 }))
    };

    /// Constant representing the empty list (nil).  Internally this is
    /// the atom `"nil"` encoded as a small atom.  It may be copied
    /// freely and does not depend on any arena.
    pub const NIL: Self = {
        let buf: [u8; 14] = [b'n', b'i', b'l', 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
        Term(Handle::Atom(TinyArray { bytes: buf, len: 3 }))
    };

    /// Produce a [`View`] of this term that borrows from the given
    /// [`Arena`].  This method decodes any inlined bytes and
    /// dereferences indexes into the arena to yield structured
    /// references.  See [`View`] for details.
    #[inline(always)]
    pub fn view<'a>(&'a self, arena: &'a Arena) -> View<'a> {
        match &self.0 {
            Handle::Int(i) => View::Int(*i),
            Handle::Real(f) => View::Real(*f),
            Handle::Date(d) => View::Date(*d),
            Handle::Var(vs) => {
                let s_bytes = &vs.bytes[..vs.len as usize];
                let s = core::str::from_utf8(s_bytes).expect("invalid UTF8 in variable");
                View::Var(s)
            }
            Handle::VarRef(vr) => {
                let name = arena.var_name(VarId(vr.index));
                View::Var(name)
            }
            Handle::Atom(a) => {
                let s_bytes = &a.bytes[..a.len as usize];
                let s = core::str::from_utf8(s_bytes).expect("invalid UTF8 in atom");
                View::Atom(s)
            }
            Handle::AtomRef(ar) => {
                let name = arena.atom_name(AtomId(ar.index));
                View::Atom(name)
            }
            Handle::Str(ss) => {
                let s_bytes = &ss.bytes[..ss.len as usize];
                let s = core::str::from_utf8(s_bytes).expect("invalid UTF8 in string");
                View::Str(s)
            }
            Handle::StrRef(sr) => {
                let slice = arena.str_slice(StrSlice {
                    index: sr.index,
                    len: sr.len,
                });
                let s = core::str::from_utf8(slice).expect("invalid UTF8 in string");
                View::Str(s)
            }
            Handle::Bin(bs) => {
                let b = &bs.bytes[..bs.len as usize];
                View::Bin(b)
            }
            Handle::BinRef(br) => {
                let slice = arena.bin_slice(BinSlice {
                    index: br.index,
                    len: br.len,
                });
                View::Bin(slice)
            }
            Handle::FuncRef(fr) => {
                let slice = arena.term_slice(TermSlice {
                    index: fr.index,
                    len: fr.len,
                });
                // Functor is the first element of the slice
                let functor = match &slice[0].0 {
                    Handle::Atom(a) => {
                        let s_bytes = &a.bytes[..a.len as usize];
                        core::str::from_utf8(s_bytes).expect("invalid UTF8 in functor")
                    }
                    Handle::AtomRef(ar2) => arena.atom_name(AtomId(ar2.index)),
                    _ => panic!("invalid functor"),
                };
                let args = &slice[1..];
                View::Func(arena, functor, args)
            }
        }
    }

    #[inline(always)]
    pub fn is_func(&self) -> bool {
        matches!(self.0, Handle::FuncRef(_))
    }

    #[inline(always)]
    pub fn is_atom(&self) -> bool {
        matches!(self.0, Handle::Atom(_) | Handle::AtomRef(_))
    }

    #[inline(always)]
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
            Handle::VarRef(v) => f.debug_struct("VarRef").field("index", &v.index).finish(),
            Handle::Atom(a) => {
                let name =
                    core::str::from_utf8(&a.bytes[..a.len as usize]).unwrap_or("<invalid utf8>");
                f.debug_struct("Atom").field("name", &name).finish()
            }
            Handle::AtomRef(a) => f.debug_struct("AtomRef").field("index", &a.index).finish(),
            Handle::Str(s) => {
                let value =
                    core::str::from_utf8(&s.bytes[..s.len as usize]).unwrap_or("<invalid utf8>");
                f.debug_struct("Str").field("value", &value).finish()
            }
            Handle::StrRef(r) => f
                .debug_struct("StrRef")
                .field("index", &r.index)
                .field("len", &r.len)
                .finish(),
            Handle::Bin(b) => {
                let slice = &b.bytes[..b.len as usize];
                f.debug_struct("Bin").field("bytes", &slice).finish()
            }
            Handle::BinRef(br) => f
                .debug_struct("BinRef")
                .field("index", &br.index)
                .field("len", &br.len)
                .finish(),
            Handle::FuncRef(fr) => f
                .debug_struct("Func")
                .field("index", &fr.index)
                .field("len", &fr.len)
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
                .field(&a.id)
                .field(&fr)
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
}

/// The typed arena used to intern atoms, variables, strings,
/// binaries and compound terms.  A `Arena` owns all memory for
/// interned data.  Terms hold only indices into this arena and remain
/// valid for the lifetime of the arena.
#[derive(Default, Clone, Debug)]
pub struct Arena {
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
    /// are appended to this vector and referenced by index/length.
    string_data: Vec<u8>,
    /// Interned binary data stored contiguously.  Binary blobs longer
    /// than the inlined capacity are appended to this vector and
    /// referenced by index/length.
    bin_data: Vec<u8>,
    /// Interned compound term slices stored sequentially.  Each slice
    /// consists of one functor atom followed by zero or more argument
    /// terms.  The `Func` handle stores the slice index and length.
    terms: Vec<Term>,
}

impl Arena {
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
    fn intern_atom(&mut self, name: &str) -> AtomId {
        // Insert the name into the set and obtain its index.  If the
        // value already exists the existing index is returned.  The
        // boolean indicates whether a new entry was inserted but is
        // unused here.
        let (index, _) = self.atoms.insert_full(name.into());
        AtomId(index as u32)
    }

    /// Intern a variable and return its id.  Variable names share a
    /// separate namespace from atoms.  Uses an `IndexSet` to assign
    /// stable indices to unique variable names.
    fn intern_var(&mut self, name: &str) -> VarId {
        let (index, _) = self.vars.insert_full(name.into());
        VarId(index as u32)
    }

    /// Access a previously interned atom by id.  Panics if the id is
    /// out of bounds.  The returned string slice is borrowed from the
    /// underlying `IndexSet` entry.
    fn atom_name<'a>(&'a self, id: AtomId) -> &'a str {
        self.atoms
            .get_index(id.0 as usize)
            .expect("invalid AtomId")
            .as_str()
    }

    /// Access a previously interned variable by id.  Panics if the id
    /// is out of bounds.  The returned string slice is borrowed from
    /// the underlying `IndexSet` entry.
    fn var_name<'a>(&'a self, id: VarId) -> &'a str {
        self.vars
            .get_index(id.0 as usize)
            .expect("invalid VarId")
            .as_str()
    }

    /// Intern a long UTF‑8 string into the arena and return its slice
    /// descriptor.  Strings are stored in a contiguous bump vector.
    fn intern_str(&mut self, s: &str) -> StrSlice {
        let index = self.string_data.len();
        self.string_data.extend_from_slice(s.as_bytes());
        let len = s.len();
        StrSlice {
            index: index as u32,
            len: len as u32,
        }
    }

    /// Intern a binary blob into the arena and return its slice descriptor.
    fn intern_bin(&mut self, bytes: &[u8]) -> BinSlice {
        let index = self.bin_data.len();
        self.bin_data.extend_from_slice(bytes);
        let len = bytes.len();
        BinSlice {
            index: index as u32,
            len: len as u32,
        }
    }

    /// Intern a compound term slice (functor + args) into the term arena.
    fn intern_func(&mut self, functor: Term, args: &[Term]) -> TermSlice {
        let index = self.terms.len() as u32;
        // Reserve space to avoid multiple reallocations when pushing.
        self.terms.reserve(args.len() + 1);
        self.terms.push(functor);
        self.terms.extend_from_slice(args);
        let len = (args.len() + 1) as u32;
        TermSlice { index, len }
    }

    /// Borrow a UTF‑8 string slice stored in the arena.  This function
    /// should not be called directly by users; instead use
    /// [`Term::view`].
    fn str_slice<'a>(&'a self, slice: StrSlice) -> &'a [u8] {
        &self.string_data[(slice.index as usize)..((slice.index + slice.len) as usize)]
    }

    /// Borrow a binary slice stored in the arena.
    fn bin_slice<'a>(&'a self, slice: BinSlice) -> &'a [u8] {
        &self.bin_data[(slice.index as usize)..((slice.index + slice.len) as usize)]
    }

    /// Borrow a contiguous slice of terms comprising a compound term.
    fn term_slice<'a>(&'a self, slice: TermSlice) -> &'a [Term] {
        &self.terms[(slice.index as usize)..((slice.index + slice.len) as usize)]
    }
}

/// Identifiers for atoms interned in an arena.  Atom identifiers are
/// opaque and refer into the [`Arena`].  They do not carry any
/// lifetime and may be copied freely.
#[derive(Debug, Clone, Copy)]
pub struct AtomId(pub u32);

/// Identifiers for variables interned in an arena.
#[derive(Debug, Clone, Copy)]
pub struct VarId(pub u32);

/// A slice descriptor for interned strings.  Contains an index into
/// the arena's `string_data` vector and a length.  Slices are
/// referenced by [`Term`] through their encoded payload.
#[derive(Debug, Clone, Copy)]
struct StrSlice {
    index: u32,
    len: u32,
}

/// A slice descriptor for interned binary blobs.
#[derive(Debug, Clone, Copy)]
struct BinSlice {
    index: u32,
    len: u32,
}

/// A slice descriptor for interned compound terms.  Contains the
/// index and length of the slice into the arena's term storage.
#[derive(Debug, Clone, Copy)]
struct TermSlice {
    index: u32,
    len: u32,
}

/// Errors that may occur when constructing terms.
#[derive(Debug, Clone)]
pub enum Error {}

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
                args_a
                    .iter()
                    .zip(args_b.iter())
                    .all(|(a, b)| a.view(arena_a) == b.view(arena_b))
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
fn kind_order(t: &View) -> u8 {
    match t {
        View::Var(_) => 0,
        View::Int(_) | View::Real(_) | View::Date(_) => 1,
        View::Atom(_) => 2,
        View::Str(_) => 3,
        View::Bin(_) => 4,
        View::Func(_, _, _) => 5,
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
        if let View::Atom(name) = a1.view(&arena) {
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
        let g = list![&mut arena; d, e, f];
        let h = tuple![&mut arena; f];
        let p = Term::func(&mut arena, "point", &[a, b, c, d, e, f, g, h]);
        let p = func![&mut arena; "foo"; Term::NIL, Term::UNIT, p, p, list![], list![&mut arena; a, b; c]];
        dbg!(&p);
        dbg!(p.view(&arena));
        assert!(p.is_func());
        if let View::Func(_, functor, args) = p.view(&arena) {
            assert_eq!(functor, "foo");
            assert_eq!(p.arity(), 6);
            assert_eq!(args.len(), 6);
        } else {
            panic!("unexpected view");
        }
    }
}
