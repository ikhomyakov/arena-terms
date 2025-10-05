//! Build script for the crate.
//!
//! This script automates lexer and parser code generation at build time,
//! using the **parlex-gen** tools (**Alex** and **ASLR**) to convert
//! grammar specification files into Rust source artifacts.
//!
//! # Overview
//! During the Cargo build process, this script is executed before
//! compilation to ensure that up-to-date lexer and parser data are
//! generated from their respective specification files. It monitors
//! both input specs for changes and triggers regeneration automatically.
//!
//! # Generation Steps
//! 1. Invokes [`parlex_gen::alex::generate`] to build lexer data from
//!    `src/term.alex` into the Cargo `OUT_DIR` as `lexer_data.rs`.
//! 2. Invokes [`parlex_gen::aslr::generate`] to build parser data from
//!    `src/termx.g` into the same directory as `parser_data.rs`.
//!
//! # Cargo Integration
//! The script emits `cargo:rerun-if-changed` directives so Cargo will
//! automatically re-run the build script if either specification file
//! is modified. It also prints human-readable warnings to the build log
//! showing input and output paths for clarity.
//!
//! # Notes
//! - This script assumes both the `parlex_gen` crate and its `alex` and
//!   `aslr` modules are available at build time.
//! - Errors in generation will cause the build to fail immediately.
use std::path::PathBuf;

/// Build-time entry point for lexer and parser generation.
///
/// Called automatically by Cargo before compilation. This function:
/// - Determines the manifest and output directories.
/// - Invokes **Alex** and **ASLR** generators to produce lexer and parser code.
/// - Emits Cargo directives to trigger regeneration on input file changes.
///
/// # Panics
/// Panics if environment variables `CARGO_MANIFEST_DIR` or `OUT_DIR`
/// are missing, or if generation fails.
fn main() {
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    let out_dir = PathBuf::from(std::env::var("OUT_DIR").unwrap());

    // --- ALEX Lexer Generation ---
    let input_file = PathBuf::from(&manifest_dir).join("src/term.alex");
    println!("cargo:rerun-if-changed={}", input_file.display());
    println!("cargo:warning=ALEX Input file is {}", input_file.display());
    println!(
        "cargo:warning=ALEX Output directory is {}",
        out_dir.display()
    );
    parlex_gen::alex::generate(&input_file, &out_dir, "lexer_data", false).unwrap();

    // --- ASLR Parser Generation ---
    let input_file = PathBuf::from(&manifest_dir).join("src/termx.g");
    println!("cargo:rerun-if-changed={}", input_file.display());
    println!("cargo:warning=ASLR Input file is {}", input_file.display());
    println!(
        "cargo:warning=ASLR Output directory is {}",
        out_dir.display()
    );
    parlex_gen::aslr::generate(&input_file, &out_dir, "parser_data", false).unwrap();
}
