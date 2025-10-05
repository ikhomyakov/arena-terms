//! Command-line interface for the `alex` lexer generator.
//!
//! This binary provides a CLI for invoking [`alex::generate`] from the command
//! line. It accepts an input `.alex` file, an optional output directory and
//! writes the generated Rust lexer code into the specified location. You can
//! run it manually to inspect the generated code.

#[cfg(feature = "cli")]
mod real {
    use clap::Parser;
    use parlex_gen::alex;
    use std::path::PathBuf;

    #[derive(Parser)]
    #[command(about = "Generate lexer code from ALEX spec")]
    struct Args {
        /// Path to the input Alex specification file.
        #[arg(short = 's', long)]
        spec: PathBuf,

        /// Path to the output directory.
        #[arg(short = 'o', long)]
        output_dir: PathBuf,

        /// Prefix used to construct output file names.
        #[arg(short = 'n', long)]
        name: String,

        /// Enable debug logging (off by default).
        #[arg(short = 'd', long)]
        debug: bool,
    }

    pub fn main() -> anyhow::Result<()> {
        let args = Args::parse();
        alex::generate(args.spec, args.output_dir, args.name, args.debug)
    }
}

#[cfg(feature = "cli")]
fn main() -> anyhow::Result<()> {
    real::main()
}

#[cfg(not(feature = "cli"))]
fn main() {
    eprintln!("lexgen disabled (compiled without `cli` feature)");
}
