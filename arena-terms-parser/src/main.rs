//! Command-line interface (CLI) for the arena-backed terms parser.
//!
//! This binary wraps the [`TermParser`] and exposes a simple command-line interface
//! for parsing Prolog-like terms backed by an [`Arena`] bump-allocator.
//! It allows reading term input from standard input or files, parsing them
//! into compact arena-allocated term representations, and printing or inspecting
//! the results.
//!
//! [`TermParser`]: arena_terms_parser::parser::TermParser
//! [`parser_oper_defs`]: arena_terms_parser::parser::parser_oper_defs
//! [`Arena`]: arena_terms::Arena

use arena_terms::{Arena, Term};
use arena_terms_parser::{TermTokenParser, define_opers};
use clap::{Parser as ClapParser, Subcommand};
use parlex::{ParlexError, Token};
use std::fs::File;
use std::io::BufReader;
use std::mem;
use try_next::TryNextWithContext;

#[derive(ClapParser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// Command
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand, Debug)]
enum Commands {
    /// Parses terms
    Parse {
        /// Input file with operator definitions
        #[arg(short, long)]
        defs: Option<String>,
        /// Input file with terms
        #[arg(short, long)]
        terms: String,
    },
    /// Prints sizes
    Sizes {},
}

fn main() -> Result<(), ParlexError> {
    env_logger::init();

    let args = Args::parse();

    match args.command {
        Commands::Parse {
            defs: defs_path,
            terms: terms_path,
        } => {
            let mut arena = Arena::try_with_default_opers().unwrap();
            let input = BufReader::new(
                File::open(&terms_path).map_err(|e| ParlexError::from_err(e, None))?,
            );
            let mut parser = TermTokenParser::try_new(input)?;
            if let Some(defs_path) = defs_path {
                let defs_input = BufReader::new(
                    File::open(&defs_path).map_err(|e| ParlexError::from_err(e, None))?,
                );
                define_opers(&mut arena, defs_input)?;
            }
            while let Some(token) = parser.try_next_with_context(&mut arena)? {
                dbg!(&parser.stats());
                dbg!(&token);
                let span = token.span().unwrap();
                let term: Option<Term> = token.value.try_into()?;
                match term {
                    Some(term) => println!("{} at {:?}", term.display(&arena), span),
                    None => println!("None at {:?}", span),
                }
            }
        }
        Commands::Sizes {} => {
            println!("Size of Term: {}", mem::size_of::<Term>());
            println!("Size of Option<Term>: {}", mem::size_of::<Option<Term>>());
            println!("Size of String: {}", mem::size_of::<String>());
            println!(
                "Size of Option<String>: {}",
                mem::size_of::<Option<String>>()
            );
            println!(
                "Size of std::string::String: {}",
                mem::size_of::<std::string::String>()
            );
            println!(
                "Size of Option<std::string::String>: {}",
                mem::size_of::<Option<std::string::String>>()
            );
        }
    }

    Ok(())
}
