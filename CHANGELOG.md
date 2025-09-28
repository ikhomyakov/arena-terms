# Release Notes

## [0.2.0] - 2025-09-28

### ⚠️  Breaking Changes
- **Removed**: `Term::is_listc()` — this function has been removed. Code relying on it will no longer compile.
- **Changed**: `Term::arity()` now supports tuples in addition to compound terms, atomic terms and lists. This changes semantics for some terms.

### ✨ Added
- New inspection helpers:
  - `kind_name()` — returns a string describing the kind of the term (`"int"`, `"atom"`, `"list"`, etc.).
  - `name()` — resolves the symbolic name of atoms, variables, or compound terms.
- A family of `unpack_*` functions for safely extracting values from terms:
  - `unpack_int`, `unpack_real`, `unpack_date`
  - `unpack_str`, `unpack_bin`
  - `unpack_atom`, `unpack_var`
  - `unpack_func_any`, `unpack_func`
  - `unpack_list`
  - `unpack_tuple_any`, `unpack_tuple`

### ✅ Tests
- Added a suite of unit tests covering:
  - Predicate functions (`is_*`)
  - `arity`, `kind_name`, and `name`
  - All `unpack_*` functions

### Upgrade Notes
- Replace calls to `is_listc` with `is_list` or direct view checks depending on your use case.
- Review usages of `arity` in your code — tuples now report their length as arity instead of `0`.
- Take advantage of the new `unpack_*` APIs for more convenient term handling.

