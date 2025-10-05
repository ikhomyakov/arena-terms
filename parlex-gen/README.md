# parlex-gen

[![Crates.io](https://img.shields.io/crates/v/parlex-gen.svg)](https://crates.io/crates/parlex-gen)
[![Documentation](https://docs.rs/parlex-gen/badge.svg)](https://docs.rs/parlex-gen)
[![License: LGPL-3.0-or-later](https://img.shields.io/badge/License-LGPL%203.0--or--later-blue.svg)](https://www.gnu.org/licenses/lgpl-3.0)
[![Rust](https://img.shields.io/badge/rust-stable-brightgreen.svg)](https://www.rust-lang.org)

Lexer and parser generator tools for Rust.

## Overview

`parlex-gen` provides two code generation tools:

- **`alex`**: Regex-based lexer generator for creating tokenizers from lexical specifications
- **`aslr`**: SLR parser generator for building parsers from grammar definitions

Both generators produce code that uses the [parlex](https://crates.io/crates/parlex) runtime library.

## Features

- Generate regex-based lexers with `alex`
- Generate SLR parsers with `aslr`

## Installation

Add this to your `Cargo.toml`:

```toml
[build-dependencies]
parlex-gen = "0.1"
```

You'll also need the runtime library:

```toml
[dependencies]
parlex = "0.1"
```

## Usage

### Lexer Generation with `alex`

Create a lexer specification file and use `alex` to generate a lexer:

```rust
// In your build.rs
use parlex_gen::alex;

fn main() {
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    let out_dir = PathBuf::from(std::env::var("OUT_DIR").unwrap());
    let input_file = PathBuf::from(&manifest_dir).join("src/lexer.alex");
    println!("cargo:rerun-if-changed={}", input_file.display());
    println!("cargo:warning=ALEX Input file is {}", input_file.display());
    println!(
        "cargo:warning=ALEX Output directory is {}",
        out_dir.display()
    );
    // Generate lexer from specification
    alex::generate(&input_file, &out_dir, "lexer_data", false).unwrap();
}
```


### Parser Generation with `aslr`

Create a grammar file and use `aslr` to generate an SLR parser:

```rust
// In your build.rs
use parlex_gen::aslr;

fn main() {
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    let input_file = PathBuf::from(&manifest_dir).join("src/parser.g");
    println!("cargo:rerun-if-changed={}", input_file.display());
    println!("cargo:warning=ASLR Input file is {}", input_file.display());
    println!(
        "cargo:warning=ASLR Output directory is {}",
        out_dir.display()
    );
    // Generate parser from specification
    aslr::generate(&input_file, &out_dir, "parser_data", false).unwrap();
}
```

## Architecture

The generation process follows these steps:

1. **Specification**: Define your lexer rules or grammar
2. **Generation**: Run `alex` and/or `aslr` to generate Rust code
3. **Integration**: The generated code uses `parlex` traits and data structures
4. **Customization**: Build your custom lexer/parser using the generated code and `parlex`

## Documentation

For detailed API documentation and examples, visit [docs.rs/parlex-gen](https://docs.rs/parlex-gen).

## License

Copyright (c) 2005–2025 IKH Software, Inc.

Released under the terms of the GNU Lesser General Public License, version 3.0 or (at your option) any later version (LGPL-3.0-or-later).

## See Also

- [parlex](https://crates.io/crates/parlex) - Runtime support library
- [Main repository](https://github.com/ikhomyakov/parlex)
