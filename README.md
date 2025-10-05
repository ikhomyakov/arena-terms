# Arena Terms

A lightweight, arena-backed representation of Prolog-like terms and parser.

## Overview

**Arena Terms** is a pair of Rust crates that provide efficient, arena-based data structures and parsing utilities for Prolog-style terms.
Together, they enable compact representation, fast allocation, and convenient manipulation of symbolic data used in logic programming or term-rewriting systems.

## Crates

### 📦 [arena-terms](./arena-terms)

[![Crates.io](https://img.shields.io/crates/v/arena-terms.svg)](https://crates.io/crates/arena-terms)
[![Documentation](https://docs.rs/arena-terms/badge.svg)](https://docs.rs/arena-terms)
[![License: LGPL-3.0-or-later](https://img.shields.io/badge/License-LGPL%203.0--or--later-blue.svg)](https://www.gnu.org/licenses/lgpl-3.0)
[![Rust](https://img.shields.io/badge/rust-stable-brightgreen.svg)](https://www.rust-lang.org)

A **Prolog-like term library** that stores immutable terms in an arena for compact, copy-by-value semantics.

This crate provides:

* `Term` — a compact, 16-byte handle for representing atoms, variables, strings, binaries, numbers, and compound structures
* `Arena` — an allocator that interns terms
* `View<'a>` — a borrowed representation for inspecting terms without allocation
* `IntoTerm` — a trait and a suite of macros (`func!`, `list!`, `tuple!`, `atom!`, `var!`, etc.) for ergonomic term construction

**Example:**

```rust
use arena_terms::{Arena, func, list, tuple, var, View};

let mut arena = Arena::new();
let term = func![
    "example";
    123, "abc",
    list![1, 2, 3],
    tuple![3.14, var!("X")],
    => &mut arena
];

if let Ok(View::Func(_, name, args)) = term.view(&arena) {
    assert_eq!(name, "example");
    assert_eq!(args.len(), 4);
}
```

**Add to your `Cargo.toml`:**

```toml
[dependencies]
arena-terms = "0.1"
```

See the [crate documentation](https://docs.rs/arena-terms) for full API details.

### 🔧 [arena-terms-parser](./arena-terms-parser)

[![Crates.io](https://img.shields.io/crates/v/arena-terms-parser.svg)](https://crates.io/crates/arena-terms-parser)
[![Documentation](https://docs.rs/arena-terms-parser/badge.svg)](https://docs.rs/arena-terms-parser)
[![License: LGPL-3.0-or-later](https://img.shields.io/badge/License-LGPL%203.0--or--later-blue.svg)](https://www.gnu.org/licenses/lgpl-3.0)
[![Rust](https://img.shields.io/badge/rust-stable-brightgreen.svg)](https://www.rust-lang.org)

A **parser** for arena-backed Prolog-like terms, built using the [`parlex`](https://crates.io/crates/parlex) and [`parlex-gen`](https://crates.io/crates/parlex-gen)

**Example:**

```rust
use arena_terms::Arena;
use arena_terms_parser::parser::TermParser;

const DEFS: &str = "[
    op('+'(x,y), infix, 380, left),
    op('*'(x,y), infix, 400, left),
]";

const TERMS: &str = "
    likes(mary, pizza).
    2 + 2 * 3 = 8 .
";

fn main() {
    let mut arena = Arena::new();

    let mut parser = TermParser::try_new(TERMS.bytes().fuse(), None).unwrap();

    parser.define_opers(&mut arena, DEFS.bytes().fuse(), None).unwrap();

    while let Some(term) = parser.try_next_term(&mut arena).unwrap() {
        println!("{}", term.display(&arena));
    }
}
```

**Add to your `Cargo.toml`:**

```toml
[dependencies]
arena-terms-parser = "0.1"
arena-terms = "0.3"
```

See the [crate documentation](https://docs.rs/arena-terms-parser) for full API details.

## Building & testing

At the repository root:

```bash
cargo build
cargo test
```

You can also build/test an individual crate with `-p`, e.g.:

```bash
cargo test -p arena-terms
```

## License

Copyright (c) 2005–2025 IKH Software, Inc.

Released under the terms of the GNU Lesser General Public License, version 3.0 or (at your option) any later version (LGPL-3.0-or-later).

## Contributing

Contributions are welcome! Please feel free to submit issues or pull requests.
