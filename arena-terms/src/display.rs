//! Defines [`TermDisplay`], a formatter for rendering [`Term`] values.
//!
//! Provides a [`fmt::Display`] implementation for human-readable output of
//! terms, including atoms, lists, tuples, and compound structures.

use crate::{Arena, Term, View};
use std::fmt;

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
            View::Date(epoch) => write!(f, "date{{{}}}", epoch_to_date_string(epoch, None)),
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
