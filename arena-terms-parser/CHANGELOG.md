# Release Notes

## [0.6.0] — 2026-04-21

### Changed

* **License changed from LGPL-3.0-or-later to MIT.**

### Dependencies

* Requires `arena-terms` 0.6.0.

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
