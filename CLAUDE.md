# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build & Test Commands

```bash
cargo build                          # Build all crates
cargo test                           # Run all tests (~146)
cargo test -p arena-terms            # Tests for core crate only
cargo test -p arena-terms-parser     # Tests for parser crate only
cargo test test_name                 # Run a single test by name
cargo test test_name -- --nocapture  # Single test with stdout
cargo clippy                         # Lint
cargo fmt --check                    # Check formatting
cargo fmt                            # Auto-format
```

### Parser CLI

```bash
cargo run -p arena-terms-parser -- parse --terms input.ax
cargo run -p arena-terms-parser -- parse --defs ops.ax --terms input.ax
cargo run -p arena-terms-parser -- parse --encoding iso-8859-1 --terms input.ax
cargo run -p arena-terms-parser -- sizes
```

## Workspace Structure

Two crates in a Cargo workspace (edition 2024, MSRV 1.89+):

- **arena-terms/** — Core library: 16-byte copyable `Term` handles, epoch-based `Arena` allocator, borrowed `View<'a>`, operator definitions, display/formatting.
- **arena-terms-parser/** — Lexer and SLR(1) parser generated from `src/term.alex` (Alex) and `src/termx.g` (ASLR) via `parlex-gen` in `build.rs`. Provides `TermLexer`, `TermParser`, `TermParserDriver`, `define_opers`, and `Encoding`. Supports multiple input encodings (UTF-8, ASCII, ISO-8859-1, Windows-1252, raw bytes) with all internal representation in UTF-8.

## Architecture

### Term → Arena → View pattern

**Term** is a 16-byte `Copy` handle that either inlines small values (atoms/vars/strings ≤14 bytes, ints, reals, dates) or references data in an Arena. Each Term carries an `ArenaID` and `EpochID` for safety checking.

**Arena** owns all interned data: `bytes: Vec<u8>` for atoms/strings/binaries, `terms: Vec<Term>` for compound term argument slices. Supports up to 8 stacked epochs with O(1) LIFO truncation for scoped allocations. Also carries the operator definition table (`OperDefs`).

**View<'a>** is the borrowed, pattern-matchable representation obtained via `term.view(&arena)`. Implements `Eq`/`Ord` following Prolog standard term order. Use View (not Term) for value-level comparison — Term equality is handle-level only.

### Parser pipeline

`term.alex` → Alex → lexer tables (`lexer_data.rs`) → `TermLexer`
`termx.g` → ASLR → parser tables (`parser_data.rs`) → `TermParser`

The `TermParserDriver` resolves operator precedence/associativity during shift-reduce decisions using the arena's `OperDefs` table. Parser produces `Term` values interned directly into the arena.

### Constructors and macros

`term.rs` provides macros (`func!`, `list!`, `tuple!`, `atom!`, `var!`) for ergonomic term construction. The `IntoTerm` trait enables implicit conversion of Rust primitives.

### Local (unpublished) dependencies

- **parlex** / **parlex-gen** (0.4.0) — Lexer/parser framework and code generators (encoding-agnostic, byte-level DFA)
- **try-next** (0.5.0) — Fallible iterator trait used by the parser

## Key Invariants

- Term handles from different arenas must not be mixed (runtime-checked via ArenaID).
- Epochs are strictly LIFO — truncate only in stack order.
- The parser rejects NaN/Inf; Display may produce unparseable output for them.
- List arity is always 0 (not Prolog cons cells). Unary tuples are unwrapped by the parser.
