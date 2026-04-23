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

use arena_terms::{Arena, Encoding, Term};
use arena_terms_parser::{TermTokenParser, define_opers};
use clap::{Parser as ClapParser, Subcommand};
use parlex::{ParlexError, Token};
use std::fs::File;
use std::io::{self, BufReader, Read, Write};
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
        /// Input encoding (any WHATWG/IANA charset name)
        #[arg(short, long, default_value = "utf-8")]
        encoding: String,
    },
    /// Decodes bytes from a given encoding to UTF-8
    Decode {
        /// Source encoding
        #[arg(short = 'f', long)]
        from: String,
        /// Input file (stdin if omitted)
        #[arg(short, long)]
        input: Option<String>,
    },
    /// Encodes UTF-8 text into a given encoding
    Encode {
        /// Target encoding
        #[arg(short = 't', long)]
        to: String,
        /// Input file (stdin if omitted)
        #[arg(short, long)]
        input: Option<String>,
    },
    /// Prints sizes
    Sizes {},
}

fn read_input(path: Option<&str>) -> Result<Vec<u8>, ParlexError> {
    let mut buf = Vec::new();
    match path {
        Some(p) => {
            File::open(p)
                .and_then(|mut f| f.read_to_end(&mut buf))
                .map_err(|e| ParlexError::from_err(e, None))?;
        }
        None => {
            io::stdin()
                .read_to_end(&mut buf)
                .map_err(|e| ParlexError::from_err(e, None))?;
        }
    }
    Ok(buf)
}

fn main() -> Result<(), ParlexError> {
    env_logger::init();

    let args = Args::parse();

    match args.command {
        Commands::Parse {
            defs: defs_path,
            terms: terms_path,
            encoding: encoding_name,
        } => {
            let encoding = Encoding::from_name(&encoding_name).ok_or_else(|| ParlexError {
                message: format!("unknown encoding: {}", encoding_name),
                span: None,
            })?;
            let mut arena = Arena::try_with_default_opers().unwrap();
            let input = BufReader::new(
                File::open(&terms_path).map_err(|e| ParlexError::from_err(e, None))?,
            );
            let mut parser = TermTokenParser::try_new(input, encoding)?;
            if let Some(defs_path) = defs_path {
                let defs_input = BufReader::new(
                    File::open(&defs_path).map_err(|e| ParlexError::from_err(e, None))?,
                );
                define_opers(&mut arena, defs_input, encoding)?;
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
        Commands::Decode {
            from: encoding_name,
            input,
        } => {
            let encoding = Encoding::from_name(&encoding_name).ok_or_else(|| ParlexError {
                message: format!("unknown encoding: {}", encoding_name),
                span: None,
            })?;
            let bytes = read_input(input.as_deref())?;
            let s = encoding
                .decode(&bytes)
                .map_err(|e| ParlexError::from_err(e, None))?;
            io::stdout()
                .write_all(s.as_bytes())
                .map_err(|e| ParlexError::from_err(e, None))?;
        }
        Commands::Encode {
            to: encoding_name,
            input,
        } => {
            let encoding = Encoding::from_name(&encoding_name).ok_or_else(|| ParlexError {
                message: format!("unknown encoding: {}", encoding_name),
                span: None,
            })?;
            let bytes = read_input(input.as_deref())?;
            let s = std::str::from_utf8(&bytes)
                .map_err(|e| ParlexError::from_err(e, None))?;
            let encoded = encoding
                .encode(s)
                .map_err(|e| ParlexError::from_err(e, None))?;
            io::stdout()
                .write_all(&encoded)
                .map_err(|e| ParlexError::from_err(e, None))?;
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
