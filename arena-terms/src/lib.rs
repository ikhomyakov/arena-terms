//! # Arena Terms
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
//! ## License
//!
//! Copyright (c) 2005–2025 IKH Software, Inc.
//!
//! Released under the terms of the GNU Lesser General Public License, version 3.0 or
//! (at your option) any later version (LGPL-3.0-or-later).

mod arena;
mod display;
mod error;
mod oper;
mod term;
mod view;

pub use arena::{Arena, ArenaID, ArenaStats, EpochID, MAX_LIVE_EPOCHS};
pub use display::TermDisplay;
pub(crate) use error::InternalTermError;
pub use error::TermError;
pub use oper::{
    Assoc, Fixity, MAX_OPER_PREC, MIN_OPER_PREC, NON_OPER_PREC, OperArg, OperDef, OperDefTab,
    OperDefs,
};
pub(crate) use term::{Handle, Slice, TinyArray};
pub use term::{IntoTerm, Term};
pub use view::View;
