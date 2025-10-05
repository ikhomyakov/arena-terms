//! Implementation of the `aslr` SLR(1) parser generator.
//!
//! This module exposes the [`generate`] function, which reads a `.g` grammar
//! specification and produces Rust source code for an SLR(1) parser.
//! The generated parser depends on the runtime traits defined in the
//! [`parlex`](https://crates.io/crates/parlex) crate. You can integrate it
//! into a `build.rs` script.

mod generate;
mod lexer;
mod parser;
mod slr;
mod symtab;

pub use generate::generate;
