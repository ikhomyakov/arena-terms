# Release Notes

## [0.6.0] — 2026-04-22

### Added

* **`Encoding` enum with `decode()` / `encode()` methods.** Supports all WHATWG encodings via
  `encoding_rs`: UTF-8, ASCII, ISO-8859-1 through 16, Windows-1250 through 1258, KOI8-R/U,
  IBM866, Shift_JIS, EUC-JP, ISO-2022-JP, GBK, GB18030, Big5, EUC-KR, UTF-16BE/LE, and more.
  `Encoding::from_name()` accepts all WHATWG/IANA charset labels (case-insensitive).

* **`TermError::Encoding` variant** for encoding/decoding errors.

### Changed

* **License changed from LGPL-3.0-or-later to MIT.**

### Dependencies

* New dependency: `encoding_rs` 0.8.

## [0.5.0] — 2026-03-20

### Breaking Changes

* **Term display: strings containing `{` and `}` are now escaped as `\{` and `\}`.**
  Previously, braces were emitted verbatim. Since bare `{` triggers string interpolation in Aware eXpress, this made `Display` output non-roundtrippable for strings containing braces.

* **Control character display format changed.**
  Previously, control characters were displayed as `\xHH\` (with a trailing backslash). This trailing backslash is not valid Aware eXpress syntax and broke roundtripping. Control characters are now displayed as `\xHH` (no trailing backslash), and common control characters use named escapes: `\a`, `\b`, `\f`, `\v`, `\e`, `\d`.

### Added

* Named escape sequences in string display: `\a` (bell), `\b` (backspace), `\f` (form feed), `\v` (vertical tab), `\e` (escape), `\d` (delete).
* Comprehensive roundtrip test suite (`string_roundtrip_vectors`) with ~50 test vectors covering all escape sequences, brace escaping, hex/octal escapes, and edge cases.

### Fixed

* `truncate_current` doc comment corrected to describe actual behavior (erases current epoch, not epoch `m`).

## [0.4.0] — 2025-10-23

### Breaking Changes

* **Crate split into submodules.** The `arena-terms` crate internals were reorganized from a single `lib.rs` into separate modules: `arena.rs`, `term.rs`, `view.rs`, `display.rs`, `error.rs`, `oper.rs`. Public API is re-exported from `lib.rs` and is unchanged.

* **Operator definitions (`oper.rs`) moved from `arena-terms-parser` to `arena-terms`.** This allows the core crate to carry default operator tables without depending on the parser.

* **`Arena::try_with_default_opers()`** — new constructor that initializes an arena with the standard operator table. Previously, operators were only available through the parser crate.

* **Lexer and parser upgraded** to work with `parlex` 0.3 and `try-next` 0.4. The parser now tracks source spans in the lexer and parser.

### Added

* `display.rs` — `TermDisplay` and `fmt::Display` implementation extracted into its own module.
* `error.rs` — `TermError` type extracted into its own module.
* `token.rs` — Token type definitions for the parser.
* Default operator table embedded in `arena-terms` via `oper.rs`.
* Source span tracking in the lexer and parser.

## [0.3.0] — 2025-09-29

### ⚠️  Breaking Changes

* **`View::Func` now carries the functor as a `&Term` (atom) instead of `&str`.**
  New shape:

  ```rust
  View::Func(&'a Arena, &'a Term, &'a [Term])
  ```

  This makes `View` consistent with other places that pass around terms, enables richer inspection of the functor (e.g., identity checks, reusing it as a term), and avoids premature string extraction.

* **`unpack_func_any`, `unpack_func`, and `unpack_list` now validate the functor as a `&Term` (atom) instead of a `&str`,** matching `View::Func`. Names are only resolved when needed via `atom_name`.


**Quick examples**

```rust
let mut arena = Arena::new();
let t = func!("foo"; 1, 2, 3 => &mut arena);

match t.view(&arena)? {
    View::Func(ar, functor, args) => {
        // functor is now `&Term` (atom), not `&str`
        assert_eq!(ar.atom_name(functor)?, "foo");
        assert_eq!(args.len(), 3);
    }
    _ => unreachable!(),
}
```

### ✨ Added

- `Term::func_name(&Arena) -> Result<&str, TermError>` to fetch a functor’s name directly.
- `Term::atom_name(&Arena)` and `Term::var_name(&Arena)` helpers for retrieving atom/variable names without using `unpack_*`.
- `Arena::func_name(&self, &Term) -> Result<&str, TermError>` for functor name lookup via the arena.
* `Term` now implements `PartialOrd`.  **Note:** the `PartialEq` and `PartialOrd` implementations operate at the **handle level**, not at the **value level**.
  This means two different `Term` handles can point to the same logical value, but still compare as unequal. Likewise, ordering reflects handle identity, not term value semantics.


### Display & pretty-printing

* Expanded docs around `TermDisplay<'a>` (`Term::display(&Arena) -> TermDisplay`) and its role as the base for future pretty-printing options. Behavior unchanged.

**Quick example**

```rust
let mut arena = Arena::new();
let t = func!("greet"; "world", 42 => &mut arena);
println!("{}", t.display(&arena));  // greet("world", 42)
```

### Upgrade Notes

* **`View::Func` now returns a functor `&Term` (atom), not `&str`.**

  * Before:

    ```rust
    if let View::Func(_, name, args) = t.view(&arena)? {
        assert_eq!(name, "foo");
    }
    ```
  * After:

    ```rust
    if let View::Func(ar, functor, args) = t.view(&arena)? {
        assert_eq!(ar.atom_name(functor)?, "foo");
    }
    ```

* **`unpack_func_any` / `unpack_func` / `unpack_list` validate by functor `&Term`.**

  * Before:

    ```rust
    let (name, args) = arena.unpack_func_any(&t, &[])?;
    if name != "foo" {
        bail!("unexpected")
    }
    ```


  * After:

      * To check name:

        ```rust
        let (functor, args) = arena.unpack_func_any(&t, &[])?;
        if arena.atom_name(functor)? != "foo" {
            bail!("unexpected")
        }
        ```
      * Or compare by term view:

        ```rust
        let foo = arena.atom("foo");
        let (functor, _) = arena.unpack_func_any(&t, &[])?;
        if functor.view(arena)? != foo.view(arena)? {
            bail!("unexpected")
        }
        ```


## [0.2.0] - 2025-09-28

### ⚠️  Breaking Changes

* **Removed**: `Term::is_listc()` — this function has been removed. Code relying on it will no longer compile.
* **Changed**: `Term::arity()` — behavior for tuples has changed.

  * **Before**: tuples always reported an arity of `0`.
  * **Now**: `arity()` returns the actual number of elements in the tuple.
  * **Lists**: still return `0` as before.
  * Other term kinds continue to behave unchanged.

### ✨ Added

- New inspection helpers:

  - `kind_name()` — returns a string describing the kind of the term (`"int"`, `"atom"`, `"list"`, etc.).
  - `name()` — resolves the symbolic name of atoms, variables, or compound terms.

- A family of `unpack_*` functions for extracting values from terms:

  - `unpack_int`, `unpack_real`, `unpack_date`
  - `unpack_str`, `unpack_bin`
  - `unpack_atom`, `unpack_var`
  - `unpack_func_any`, `unpack_func`
  - `unpack_list`
  - `unpack_tuple_any`, `unpack_tuple`

- **`TermDisplay` adapter for formatting**:

  - New `pub struct TermDisplay<'a> { term: &'a Term, arena: &'a Arena }` which pairs a `Term` with its `Arena` for rendering.
  - `impl fmt::Display for TermDisplay<'_>` so terms can be printed with standard formatting macros.
  - `Term::display(&self, arena: &Arena) -> TermDisplay` helper for the common case.
  - Typical usage:

    ```rust
    use arena_terms::{Term, Arena, func, IntoTerm};

    let mut arena = Arena::new();
    let term = func!("foo"; 1, "hello, world!" => &mut arena);

    println!("{}", term.display(&arena));
    ```

### ✅ Tests

- Added a suite of unit tests covering:

  - Predicate functions (`is_*`)
  - `arity`, `kind_name`, and `name`
  - All `unpack_*` functions
  - **Display formatting via `TermDisplay`** (including nested terms, lists, tuples, and atoms)

### Upgrade Notes
- Replace calls to `is_listc` with `is_list` or direct view checks depending on your use case.
- Review usages of `arity` in your code — tuples now report their length as arity instead of `0`.
- Take advantage of the new `unpack_*` APIs for more convenient term handling.
* To print terms, prefer `term.display(&arena)`.

