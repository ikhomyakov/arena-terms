# Release Notes

## [0.6.0] — 2026-04-22

### Breaking Changes

* **All parser entry points now require an `Encoding` parameter.**
  `TermLexer::try_new`, `TermTokenParser::try_new`, `TermParser::try_new`, and `define_opers`
  all take an `Encoding` argument. Use `Encoding::Utf8` for previous behavior.

### Added

* **Multi-encoding support.** `Encoding` enum (from `arena-terms`) with `decode()`/`encode()`
  methods supports all WHATWG encodings via `encoding_rs`. All internal term representation
  remains UTF-8. Binary content (`bin{...}`) always collects raw source bytes.

* **CLI `--encoding` flag.** The `parse` subcommand accepts `--encoding` (default `utf-8`).

* **Outer parentheses around double-quoted strings** (matching legacy parser behavior).
  `"a{expr}b"` now emits `( STR ++ ( expr ) ++ STR )`, isolating the interpolated string from
  surrounding operators. For bare strings, the parser's unary-tuple unwrapping collapses them.

* Regression tests for CRLF normalization in strings, atoms, script blocks, bin{}, and text{}.
* Regression tests for string interpolation with prefix operators and function arguments.

### Fixed

* **CRLF normalization in quoted strings and atoms.** `\r\n` inside `"..."` and `'...'` is now
  normalized to `\n`, matching legacy behavior. Bare `\r` and bare `\n` are preserved as-is.

* **CRLF normalization in script blocks `{...}`.** Legacy normalizes `\r\n` → `\n`; arena-terms
  previously preserved it verbatim. Fixed by excluding `\r\n` from the `ScriptNotBraces` DFA
  pattern so the `ScriptNewLine` action fires.

* **`bin{N:...}` CRLF data loss.** The `BinCountNLChar` action incorrectly stripped `\r` from
  the accumulation buffer (checking `buffer[0]` instead of the buffer tail), losing a byte and
  producing wrong byte counts. Binary content now preserves all raw bytes verbatim.

* **`text{N:...}` CRLF normalization at non-leading positions.** Same `buffer[0]` bug as bin{};
  the `\r` strip only triggered when `\r` happened to be the first byte of all counted content.
  Now checks the buffer tail correctly.

* **Trace logging no longer panics on non-UTF-8 buffers.** Replaced `str::from_utf8` with
  `String::from_utf8_lossy` in debug trace output.

### Changed

* **License changed from LGPL-3.0-or-later to MIT.**

* Refactored `take_str` / `take_bytes` from free functions into `TermLexerDriver` methods,
  matching `take_str2` / `take_bytes2` symmetry.

### Known Divergences from Legacy

* **`123e5` is accepted as a float literal.** The legacy parser requires a decimal point
  (`1.23e5`), treating `123e5` as integer `123` followed by atom `e5`. Arena-terms accepts
  the `DEC+EXP` form (`123e5` = `1.23e7`) as valid, following C/Python/JSON/Rust conventions.
  ISO Prolog also requires a decimal point, but SWI-Prolog accepts this form.

* **Date representation.** Legacy uses Excel serial dates (double); arena-terms uses Unix
  epoch milliseconds (i64) with extended ISO-8601 format support.

### Dependencies

* Requires `arena-terms` 0.6.0.
* Requires `parlex` 0.4.1 and `try-next` 0.5.0.
* New dependency: `encoding_rs` 0.8.

## [0.5.0] — 2026-03-20

### Added

* Comprehensive `string_roundtrip_vectors` test suite with ~50 test vectors covering all escape sequences, brace escaping (`\{`, `\}`), hex/octal escapes, named control character escapes, and edge cases.

### Changed

* Updated `more_complicated_term` test expectation to reflect new brace escaping in `arena-terms` display (`{` → `\{`, `}` → `\}`).

### Dependencies

* Requires `arena-terms` 0.5.0 (brace escaping in string display).

## [0.4.0] — 2025-10-23

### Breaking Changes

* **Upgraded to `parlex` 0.3 and `try-next` 0.4.** Parser internals rewritten to use the new `parlex` API.

* **`oper.rs` moved to `arena-terms` crate.** Operator definitions are now part of the core crate, not the parser. The parser re-exports them for convenience.

* **Source span tracking.** The lexer and parser now track source positions (line/column) for better error messages.

### Added

* `token.rs` — Token type definitions extracted into a separate module.
* CLI binary restructured: moved from `src/bin/arena_terms_parser.rs` to `src/main.rs`.

### Changed

* Lexer rewritten for `parlex` 0.3 compatibility.
* Parser rewritten for `parlex` 0.3 compatibility with improved error reporting.
