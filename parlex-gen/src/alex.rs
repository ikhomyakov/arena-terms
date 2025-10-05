//! Implementation of the `alex` lexer generator.
//!
//! This module exposes the [`generate`] function, which reads an `.alex` lexical
//! specification and produces Rust source code for a deterministic finite
//! automaton (DFA)‑based lexer. It leverages the [`regex_automata`] crate to
//! compile the regular expressions and emits code that depends on the
//! [`parlex`](https://crates.io/crates/parlex) runtime library.
//! You can integrate it into a `build.rs` script.

use anyhow::{Context, Result, anyhow, bail};
use once_cell::sync::Lazy;
use regex::{Captures, Regex};
use regex_automata::{
    MatchKind,
    dfa::{StartKind, dense},
    nfa::thompson::{Config as ThomConfig, NFA},
    util::syntax,
};
use std::collections::{HashMap, HashSet};
use std::io::Write;
use std::path::Path;

/// Represents a named regular expression used in lexer definitions.
///
/// Each instance stores the rule label and the resolved regular expression
/// after variable substitution.
#[derive(Debug, Clone)]
struct LRegex {
    /// The label identifying the regex rule.
    label: String,

    /// The regular expression
    regex: String,
}

/// Represents a single lexer rule definition.
///
/// A lexer rule associates a label with one or more active lexer modes
/// and a regular expression pattern to match.
#[derive(Debug, Clone)]
struct LexRule {
    /// The label identifying the lexer rule.
    label: String,

    /// The lexer modes in which this rule is active.
    modes: Vec<String>,

    /// The resolved regular expression, after variable substitution.
    regex: String,

    /// The source line number of this rule in the lexer specification.
    line_no: usize,
}

/// Represents a parsed lexer specification.
///
/// Contains variable definitions and fully expanded lexer rules after
/// performing variable substitutions.
#[derive(Debug, Default)]
struct Parsed {
    /// The mapping of variable names to their raw values defined in the lexer source.
    vars: HashMap<String, String>,

    /// The list of lexer rules with resolved and expanded regular expressions.
    rules: Vec<LexRule>,
}

/// Regular expression for matching variable definitions in the form:
/// ```text
/// NAME = VALUE
/// ```
static VAR_DEF_RE: Lazy<Regex> =
    Lazy::new(|| Regex::new(r#"^([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(.*)$"#).unwrap());

/// Regular expression for matching lexer rule definitions in the form:
/// ```text
/// LABEL: <modes> pattern
/// ```
static LEX_RULE_RE: Lazy<Regex> =
    Lazy::new(|| Regex::new(r#"^([A-Za-z_][A-Za-z0-9_]*)\s*:\s*<([^>]*)>\s*(.+)$"#).unwrap());

/// Regular expression for detecting variable placeholders in the form:
/// ```text
/// {{ VAR_NAME }}
/// ```
static VAR_IN_REGEX_RE: Lazy<Regex> =
    Lazy::new(|| Regex::new(r#"\{\{\s*([A-Za-z_][A-Za-z0-9_]*)\s*\}\}"#).unwrap());

/// Determines the smallest unsigned integer type capable of representing `n` elements.
///
/// Returns `"u8"` if `n` fits within 8 bits, otherwise `"u16"`.
///
/// # Panics
/// Panics if `n` exceeds `u16::MAX + 1`.
fn calculate_minimum_unsigned_type(n: usize) -> &'static str {
    assert!(n <= u16::MAX as usize + 1);
    if n <= (u8::MAX as usize) + 1 {
        "u8"
    } else {
        "u16"
    }
}

/// Generates lexer code from a specification file into a Rust source file.
///
/// Reads the lexer spec at `spec_path`, expands variables, parses rules/modes,
/// and writes the generated lexer to `output_dir/output_name`.
///
/// # Parameters
/// - `spec_path`: Path to the lexer specification file.
/// - `output_dir`: Destination directory for the generated Rust file.
/// - `output_name`: Basename (without extension) of the generated file.
/// - `_output_debug_info`: When `true`, may include extra debug metadata (reserved).
///
/// # Errors
/// Returns an error if the spec cannot be read or parsed, if variable expansion
/// fails, or if code generation/output fails.
pub fn generate<P: AsRef<Path>>(
    spec_path: P,
    output_dir: P,
    output_name: impl AsRef<str>,
    _output_debug_info: bool,
) -> Result<()> {
    let output_dir = output_dir.as_ref();
    let output_name = output_name.as_ref();
    let spec = std::fs::read_to_string(&spec_path)?;
    let (rules, modes, _vars, start_mode) = parse_alex(&spec)?;
    let Some(start_mode) = start_mode else {
        bail!("Cannot determine start mode");
    };

    let mut rule_vecs: HashMap<String, Vec<LRegex>> =
        modes.iter().cloned().map(|key| (key, Vec::new())).collect();

    for r in &rules {
        for m in &r.modes {
            if m == "*" {
                for m in modes.iter() {
                    rule_vecs
                        .get_mut(m)
                        .ok_or(anyhow!("Missing mode {:?}", m))?
                        .push(LRegex {
                            label: r.label.clone(),
                            regex: r.regex.clone(),
                        });
                }
            } else {
                rule_vecs
                    .get_mut(m)
                    .ok_or(anyhow!("Missing mode {:?}", m))?
                    .push(LRegex {
                        label: r.label.clone(),
                        regex: r.regex.clone(),
                    });
            }
        }
    }

    let mut out = std::fs::File::create(output_dir.join(output_name).with_extension("rs"))?;

    writeln!(out, "/*")?;
    writeln!(out, "Generated by ALEX")?;
    writeln!(out, "Copyright (c) 2005-2025 IKH Software, Inc.")?;
    writeln!(out, "*/\n")?;
    writeln!(out, "use include_bytes_aligned::include_bytes_aligned;")?;
    writeln!(
        out,
        "use parlex::{{LexerMode, LexerRule, LexerData, Lexer, LexerCtx, Token}};\n"
    )?;

    let mut modes: Vec<_> = modes.iter().filter(|&s| s != "*").collect();
    modes.sort();

    writeln!(out, "#[derive(Debug, Clone, Copy, PartialEq, Eq)]")?;
    writeln!(
        out,
        "#[repr({})]",
        calculate_minimum_unsigned_type(modes.len())
    )?;
    writeln!(out, "pub enum Mode {{")?;
    for (i, m) in modes.iter().enumerate() {
        writeln!(out, "    {} = {},", m, i)?;
    }
    writeln!(out, "}}\n")?;
    writeln!(out, "impl LexerMode for Mode {{")?;
    writeln!(out, "    const COUNT: usize = {};", modes.len())?;
    writeln!(out, "}}\n")?;
    writeln!(out, "impl From<Mode> for usize {{")?;
    writeln!(out, "    fn from(m: Mode) -> Self {{")?;
    writeln!(out, "        m as usize")?;
    writeln!(out, "    }}")?;
    writeln!(out, "}}\n")?;

    writeln!(out, "#[derive(Debug, Clone, Copy, PartialEq, Eq)]")?;
    writeln!(
        out,
        "#[repr({})]",
        calculate_minimum_unsigned_type(rules.len() + 2)
    )?;
    writeln!(out, "pub enum Rule {{")?;
    writeln!(out, "    Empty = 0,")?;
    for (i, r) in rules.iter().enumerate() {
        writeln!(
            out,
            "    {} = {}, // <{}> {}",
            r.label,
            i + 1,
            r.modes.join(","),
            r.regex
        )?;
    }
    writeln!(out, "    End = {},", rules.len() + 1)?;
    writeln!(out, "}}\n")?;
    writeln!(out, "impl LexerRule for Rule {{")?;
    writeln!(out, "    const COUNT: usize = {};", rules.len() + 2)?;
    writeln!(out, "    const END: Self = Self::End;")?;
    writeln!(out, "}}\n")?;
    writeln!(out, "impl From<Rule> for usize {{")?;
    writeln!(out, "    fn from(r: Rule) -> Self {{")?;
    writeln!(out, "        r as usize")?;
    writeln!(out, "    }}")?;
    writeln!(out, "}}\n")?;

    let max_mode_rules = rule_vecs.values().map(|v| v.len()).max().unwrap_or(0);

    writeln!(out, "pub struct LexData;")?;
    writeln!(out, "impl LexData {{")?;
    writeln!(out, "    const START_MODE: Mode = Mode::{};\n", start_mode)?;
    writeln!(
        out,
        "    const TAB: &'static [[Rule; {}]] = &[",
        max_mode_rules
    )?;

    for (i, m) in modes.iter().enumerate() {
        writeln!(out, "        /* MODE {} {:?} */ [", i, m)?;
        let rules = rule_vecs.get(*m).ok_or(anyhow!("Missing mode {:?}", m))?;
        for r in rules.iter() {
            writeln!(out, "            Rule::{},", r.label)?;
        }
        for _ in rules.len()..max_mode_rules {
            writeln!(out, "            Rule::Empty,")?;
        }
        writeln!(out, "        ],")?;
    }
    writeln!(out, "    ];\n")?;

    let mut file_le = std::fs::File::create(output_dir.join(output_name).with_extension("dfale"))?;
    let mut file_be = std::fs::File::create(output_dir.join(output_name).with_extension("dfabe"))?;

    writeln!(out, "    #[cfg(target_endian = \"little\")]")?;
    writeln!(
        out,
        "    const DFA_BYTES: &[u8] = include_bytes_aligned!(4, \"{}.dfale\");",
        output_name
    )?;
    writeln!(out, "    #[cfg(target_endian = \"big\")]")?;
    writeln!(
        out,
        "    const DFA_BYTES: &'static [u8] = include_bytes_aligned!(4, \"{}.dfabe\");\n",
        output_name
    )?;

    let mut offset = 0;
    writeln!(out, "    const DFA_OFFSETS: &'static [usize] = &[")?;

    for m in modes.iter() {
        let rules = rule_vecs.get(*m).ok_or(anyhow!("Missing mode {:?}", m))?;
        let mut hirs = Vec::new();
        let conf = syntax::Config::new().utf8(false);
        for r in rules.iter() {
            hirs.push(syntax::parse_with(&r.regex, &conf).with_context(|| {
                format!(
                    "Failed to parse regex {} for mode {:?} rule {:?}",
                    r.regex, m, r.label
                )
            })?);
        }

        let nfa = NFA::compiler()
            .configure(ThomConfig::new().utf8(false))
            .build_many_from_hir(&hirs)?;
        let dfa = dense::Builder::new()
            .configure(
                dense::DFA::config()
                    .match_kind(MatchKind::All)
                    .start_kind(StartKind::Anchored),
            )
            .build_from_nfa(&nfa)?;

        let (bytes, pad) = dfa.to_bytes_little_endian();
        assert!((bytes.len() - pad) % 4 == 0);
        file_le.write_all(&bytes[pad..])?;

        let (bytes, pad) = dfa.to_bytes_big_endian();
        assert!((bytes.len() - pad) % 4 == 0);
        file_be.write_all(&bytes[pad..])?;

        writeln!(out, "        {}, // {}", offset, m)?;
        offset += bytes.len() - pad;
    }
    writeln!(out, "    ];")?;
    writeln!(out, "}}\n")?;

    writeln!(out, "impl LexerData for LexData {{")?;
    writeln!(out, "    type LexerMode = Mode;")?;
    writeln!(out, "    type LexerRule = Rule;\n")?;
    writeln!(out, "    #[inline]")?;
    writeln!(out, "    fn start_mode() -> Self::LexerMode {{")?;
    writeln!(out, "        Self::START_MODE")?;
    writeln!(out, "    }}")?;
    writeln!(out, "    #[inline]")?;
    writeln!(out, "    fn dfa_bytes() -> &'static [u8] {{")?;
    writeln!(out, "        Self::DFA_BYTES")?;
    writeln!(out, "    }}")?;
    writeln!(out, "    #[inline]")?;
    writeln!(out, "    fn dfa_offsets() -> &'static [usize] {{")?;
    writeln!(out, "        Self::DFA_OFFSETS")?;
    writeln!(out, "    }}")?;
    writeln!(out, "    #[inline]")?;
    writeln!(
        out,
        "    fn lookup(mode: Self::LexerMode, pattern_id: usize) -> Self::LexerRule {{"
    )?;
    writeln!(
        out,
        "        Self::TAB[Into::<usize>::into(mode)][pattern_id]"
    )?;
    writeln!(out, "    }}")?;
    writeln!(out, "}}\n")?;

    Ok(())
}

/// Parses an Alex-style lexer specification into rules, modes, and variables.
///
/// Performs syntactic parsing only; variable expansion is handled separately
/// by [`expand_vars`].
///
/// # Returns
/// - `Vec<LexRule>`: Collected lexer rules (regex not yet re-expanded unless
///   the input already had literals).
/// - `HashSet<String>`: Declared lexer mode names.
/// - `HashMap<String, String>`: Variable definitions (`NAME -> raw value`).
/// - `Option<String>`: Optional start mode label (if specified).
///
/// # Errors
/// Returns an error if the input does not conform to the expected format.
fn parse_alex(
    input: &str,
) -> Result<(
    Vec<LexRule>,
    HashSet<String>,
    HashMap<String, String>,
    Option<String>,
)> {
    let mut rules: Vec<LexRule> = Vec::new();
    let mut modes: HashSet<String> = HashSet::new();
    let mut vars: HashMap<String, String> = HashMap::new();
    let mut start_mode: Option<String> = None;

    for (i, raw_line) in input.lines().enumerate() {
        let line_no = i + 1;
        let line = raw_line.trim();

        if line.is_empty() || line.starts_with("--") {
            continue;
        }

        if let Some(cap) = VAR_DEF_RE.captures(line) {
            let name = cap[1].to_string();
            let value = expand_vars(cap[2].trim(), &vars)?;
            vars.insert(name, value);
            continue;
        }

        if let Some(cap) = LEX_RULE_RE.captures(line) {
            let label = cap[1].to_string();
            let modes_str = cap[2].trim();
            let regex = expand_vars(cap[3].trim(), &vars)?;

            let rule_modes: Vec<String> = modes_str
                .split(',')
                .map(|s| s.trim().to_string())
                .filter(|s| !s.is_empty())
                .collect();

            if start_mode.is_none() && !rule_modes.is_empty() {
                start_mode = Some(rule_modes[0].clone());
            }

            modes.extend(rule_modes.iter().cloned());

            if rule_modes.is_empty() {
                bail!("No modes found at line ({}): {:?}", line_no, line);
            }

            rules.push(LexRule {
                label,
                modes: rule_modes,
                regex,
                line_no,
            });
            continue;
        }

        bail!("Unrecognized line ({}): {:?}", line_no, line);
    }

    Ok((rules, modes, vars, start_mode))
}

/// Expands `{{VAR}}` placeholders using the provided variable map.
///
/// # Parameters
/// - `input`: Text containing `{{ NAME }}` placeholders.
/// - `vars`: Map of variable names to raw values used for substitution.
///
/// # Returns
/// The input string with all placeholders expanded.
///
/// # Errors
/// Returns an error if an undefined variable is referenced or if expansion fails.
fn expand_vars(input: &str, vars: &HashMap<String, String>) -> Result<String> {
    let mut out = input.to_string();
    let mut seen_any = true;
    let mut depth = 0;

    while seen_any {
        depth += 1;
        if depth > 64 {
            bail!(
                "Variable expansion exceeded depth (possible cycle): {}",
                input
            );
        }

        seen_any = false;
        let mut missing: HashSet<String> = HashSet::new();

        out = VAR_IN_REGEX_RE
            .replace_all(&out, |caps: &Captures| {
                let name = caps[1].to_string();
                if let Some(val) = vars.get(&name) {
                    seen_any = true;
                    format!("(?:{})", val)
                } else {
                    missing.insert(name.clone());
                    caps.get(0).unwrap().as_str().to_string()
                }
            })
            .to_string();

        if !missing.is_empty() {
            let list = missing.into_iter().collect::<Vec<_>>().join(", ");
            bail!("Unknown variable(s): {}", list);
        }
    }
    Ok(out)
}

/// Unit tests for the lexer specification parser.
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_example() {
        let input = r#"
SPACE = (?-u:[ \t\f])
ATOM = (?-u:([a-z]([a-z]|[A-Z_]|[0-9])*)|[-~@#$^&*+=<>:.?/!;]+)
VAR = (?-u:[A-Z_]([a-z]|[A-Z_]|[0-9])*)
HEX_CONST = (?-u:0x[0-9a-fA-F]*)
OCT_CONST = (?-u:0[0-7]*)
DEC_CONST = (?-u:[1-9][0-9]*)
FP_CONST = (?-u:([0-9]*\.[0-9]+([eE][+-]?[0-9]+)?)|([0-9]+\.[0-9]*([eE][+-]?[0-9]+)?))
LABEL = (?-u:[a-z]([a-z]|[A-Z_]|[0-9])*)
NEW_LINE = (?-u:(\r?\n))

Expr1: <Expr> %.*
Expr2: <Expr, Comment> (?-u:/\*)
Comment1: <Comment> (?-u:\*/)
Comment2: <Comment> [^*\r\n]
Expr3: <Expr> {{SPACE}}
Expr4: <Expr, Comment> {{NEW_LINE}}
Comment3: <Comment> .
Expr5: <Expr> (?-u:\()
Expr6: <Expr> (?-u:\))
Expr7: <Expr> (?-u:\[)

"#;

        let (rules, modes, vars, start_mode) = parse_alex(input).unwrap();
        assert!(vars.contains_key("SPACE"));
        assert_eq!(rules.len(), 10);
        assert_eq!(modes.len(), 2);
        assert_eq!(start_mode.as_deref(), Some("Expr"));

        let r = rules.iter().find(|r| r.label == "Expr3").unwrap();
        assert!(r.regex.starts_with("(?:"));
        assert!(r.modes.contains(&"Expr".to_string()));
    }
}
