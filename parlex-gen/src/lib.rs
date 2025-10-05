//! Copyright (c) 2005–2025 IKH Software, Inc.
//!
//! Released under the terms of the GNU Lesser General Public License, version 3.0
//! or (at your option) any later version (LGPL-3.0-or-later).
//!
//! Lexer and parser generators.
//!
//! `parlex-gen` provides two generators:
//!  * **`alex`** — a regular-expression–based lexer generator
//!  * **`aslr`** — an SLR(1) parser generator
//!
//! For more background and examples, see the `parlex-gen` README on GitHub and
//! docs.rs.
//!
//! # Crates.io
//! Published at [crates.io/crates/parlex-gen](https://crates.io/crates/parlex-gen).

pub mod alex;
pub mod aslr;
