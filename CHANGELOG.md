# Release Notes

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

