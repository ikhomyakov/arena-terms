//! Command-line interface for the `aslr` parser generator.
//!
//! This binary wraps the [`aslr::generate::generate`] function and exposes
//! command-line options for generating an SLR parser from a grammar
//! specification. It reads an input `.g` file and writes the generated
//! parser code.

#[cfg(feature = "cli")]
mod real {
    use clap::Parser;
    use parlex_gen::aslr;
    use std::path::PathBuf;

    #[derive(Parser)]
    #[command(about = "Generate parser code from ASLR grammar")]
    struct Args {
        /// Path to the input ASLR grammar file
        #[arg(short = 'g', long)]
        grammar: PathBuf,

        /// Path to the output directory.
        #[arg(short = 'o', long)]
        output_dir: PathBuf,

        /// Prefix used to construct output file name
        #[arg(short = 'n', long)]
        name: String,

        /// Enable debug logging (off by default).
        #[arg(short = 'd', long)]
        debug: bool,
    }

    pub fn main() -> anyhow::Result<()> {
        let args = Args::parse();
        aslr::generate(args.grammar, args.output_dir, args.name, args.debug)
    }
}

#[cfg(feature = "cli")]
fn main() -> anyhow::Result<()> {
    real::main()
}

#[cfg(not(feature = "cli"))]
fn main() {
    eprintln!("pargen disabled (compiled without `cli` feature)");
}
