//! Defines [`View`], a borrowed read-only representation of a [`Term`].
//!
//! Provides lightweight accessors for inspecting terms without allocation.

use crate::{Arena, Handle, Term, TermError};
use core::fmt;
use std::cmp::Ordering;

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

impl Term {
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
}

impl Arena {
    /// Produce a [`View`] of the given `term` that borrows from
    /// this [`Arena`].  This method decodes any inlined bytes and
    /// dereferences indexes into the arena to yield structured
    /// references.  See [`View`] for details.
    #[inline]
    pub fn view<'a>(&'a self, term: &'a Term) -> Result<View<'a>, TermError> {
        term.view(self)
    }
}

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

#[cfg(test)]
mod tests {
    use super::*;
    use std::fmt::Write;

    #[test]
    fn view_size_is_40_bytes() {
        assert_eq!(core::mem::size_of::<View>(), 40);
    }

    #[test]
    fn option_view_size_is_40_bytes() {
        assert_eq!(core::mem::size_of::<Option<View>>(), 40);
    }
}
