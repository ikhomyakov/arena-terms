# Review: `arena-terms` & `arena-terms-parser` — bugs, non-idiomatic Rust, smells

**Reviewer:** Claude (Fable 5) — 2026-07-05
**Scope:** every `.rs` file in both crates plus `term.alex`, `termx.g`, `build.rs`,
manifests. Workspace v0.6.2, edition 2024, MSRV 1.89.

**Verification.** Shipped test suite is green (137/137). Every finding marked
**[probe-confirmed]** was reproduced with a temporary integration test compiled against the
workspace (probe files were deleted afterwards); the probe output is quoted. `cargo clippy
--all-targets` currently **fails** (one `deny`-level lint in tests) and emits ~100
warnings; `cargo fmt --check` **fails** (§F).

Companion report: `fable5-review-arena-cpp.md` (gap analysis vs the legacy C++
implementation). Cross-references B2–B10 below are cited there.

---

## A. Confirmed bugs (probe-backed), most severe first

### B1. `intern_func`/`intern_seq` interleave nested allocations → silent term corruption
`arena.rs:627-682`, `term.rs:194-202`.

`Arena::intern_func` pushes the functor, then converts each `IntoTerm` item **while
appending to the same `terms` vector**:

```rust
let index = self.terms.len();
self.terms.push(functor);
for x in args {
    let t = x.into_term(self);   // may itself intern a compound into self.terms!
    self.terms.push(t);
}
let len = self.terms.len() - index;
```

Because `impl IntoTerm for F: FnOnce(&mut Arena) -> Term` exists (`term.rs:194`) — and is
advertised in the crate's own test (`into_test`: *"You can also provide closures returning
Term"*) — an argument can allocate a nested compound *between* pushes. The nested slice
lands inside the outer slice and the outer `len` counts it:

```rust
let t = Term::func(&mut a, "outer",
    [|ar: &mut Arena| ar.func("inner", [Term::int(1), Term::int(2)])]);
// PROBE display = outer(inner, 1, 2, inner(1, 2))
// PROBE arity   = 4        (expected 1)
```

**[probe-confirmed]** No error, no panic — a silently wrong term. The same hazard exists in
`intern_seq` and `intern_seq_plus_one` (so `arena.list([closure, …])`, `listc`, `tuple`),
and in `Term::func`'s lazily-consumed `IntoIterator` (a caller-supplied iterator whose
`next()` allocates has the same effect — it doesn't need the closure impl).

The macros (`func!`, `list!`, `tuple!`) are immune because they evaluate all arguments into
a `&[Term]` *before* calling the arena — which is exactly the fix:

* **Fix:** two-phase interning — collect converted args into a scratch buffer (a reusable
  `Vec<Term>` on the `Arena`, or `SmallVec`) and only then extend `self.terms`. Do the same
  in all three `intern_*` functions.
* Alternatively (weaker): keep single-phase but `debug_assert_eq!(self.terms.len(), index +
  pushed_so_far)` after each conversion to at least catch it.

### B2. `truncate` does not refresh the epoch ID → stale handles silently alias new data
`arena.rs:177-185`.

`truncate(epoch)` rewinds `bytes`/`terms` and sets `current_epoch = epoch`, but keeps
`epoch_ids[epoch]` unchanged. A handle created in that epoch *before* truncation still
carries the same epoch ID and an in-range index once new data is allocated:

```rust
let stale = a.str("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
a.truncate_current().unwrap();
let _new  = a.str("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbb");
stale.view(&a)   // PROBE: Ok(Str("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"))
```

**[probe-confirmed]** The entire point of random epoch IDs is to reject stale handles (the
`stale_term_str` unit test checks the empty-arena case, which happens to fail the length
check), but the ID survives truncation, so refill re-validates old handles against
unrelated bytes.

This is not just a logic bug — it is a **soundness hole in waiting**: `view()` builds
`&str` via `core::str::from_utf8_unchecked` (`view.rs:94-127`). A stale `StrRef/AtomRef/
VarRef` whose byte range is later re-occupied by a **binary** (`intern_bytes` shares the
same `bytes` vec) yields a `&str` over non-UTF-8 bytes — instant UB territory.

* **Fix:** in `truncate`, regenerate `self.epoch_ids[epoch] = EpochID(rand::random())`
  (the truncated-to epoch is erased *and reused*, so it must get a fresh identity). That
  one line closes both the aliasing and the UB path.
* Consider also zeroing/refreshing the IDs of the higher erased epochs for hygiene (they
  are unreachable via `epoch_index`'s `[..=current_epoch]` bound, but cheap to clear).

### B3. `View::eq` compares functors by handle → structural equality fails; `Eq`/`Ord` disagree
`view.rs:206-217` vs `view.rs:276-300`.

`PartialEq` for `View::Func` short-circuits on `functor_a != functor_b` — a **`Term` handle
comparison** (derived `PartialEq` on `Handle`, including `Slice{epoch_id,index,len}`).
Since the arena never dedups (see companion report §2.2), two same-named functors longer
than 14 bytes occupy different slices:

```rust
let f1 = a.func("very_long_functor_name_over_14_bytes", [Term::int(1)]);
let f2 = a.func("very_long_functor_name_over_14_bytes", [Term::int(1)]);
// PROBE: v1 == v2  -> false
// PROBE: v1.cmp(&v2) -> Equal
```

**[probe-confirmed]** Two violations at once:

1. Structurally identical terms compare unequal (only for long functor names — a nasty
   heisenbug threshold at 15 bytes).
2. `Ord::cmp` (which *does* view the functors, `view.rs:281-284`) says `Equal` while
   `PartialEq` says `false` — breaking the `Eq`/`Ord` consistency contract. `BTreeMap`,
   `sort`+`dedup`, `binary_search` all misbehave on such keys.

* **Fix:** compare functors via their views (`functor_a.view(arena_a) ==
  functor_b.view(arena_b)`), or intern atoms (fixes the root cause), or — most robust —
  implement `PartialEq` as `self.cmp(other) == Ordering::Equal` so the two impls cannot
  drift (with the numeric caveats of B4/B9 fixed inside `cmp`).

### B4. Same-kind integers (and dates) compared through `f64` → precision loss above 2^53
`view.rs:188-196`, `258-266`, `numeric_value` at `view.rs:368-375`.

```rust
Term::int(1 << 53) == Term::int((1 << 53) + 1)   // PROBE: views compare EQUAL
```

**[probe-confirmed]** `numeric_value` converts `Int(i64)`/`Date(i64)` to `f64` even when
both sides are the same kind. Distinct i64 values ≥ 2^53 compare equal and unordered
(`total_cmp` → `Equal`). The C++ implementation compared ints exactly; this is a regression.

* **Fix:** in both `eq` and `cmp`, match `(Int(a), Int(b)) => a == b / a.cmp(b)` and
  `(Date(a), Date(b))` likewise; use the float path only for `Real` (or for mixed kinds if
  you adopt value-ordering — see B5).

### B5. Mixed-kind numeric comparison is dead code; `kind_order` contradicts its own comment
`view.rs:180-196` (eq), `250-266` (cmp), `346-362` (kind_order).

Both `eq` and `cmp` first gate on `kind_order`, returning early when the kinds differ. The
`(Int|Real|Date, Int|Real|Date)` arm annotated *"compare by numeric value irrespective of
the exact type"* can therefore only ever see **same-kind** pairs:

```rust
// PROBE: Int(1) == Real(1.0) -> false ; Int(1).cmp(Real(1.0)) -> Less (kind order)
```

**[probe-confirmed]** Additionally the `kind_order` doc comment says *"variables < numbers
< atoms < strings < binaries < compounds"* while the code places `Bin` **after** compounds
(`Func=6, Tuple=7, List=8, Bin=9`). Decide the semantics once:

* If kind-first ordering is intended (matches C++ behavior in spirit): delete the dead
  mixed-kind arms, fix the comments, and compare ints exactly (B4).
* If Prolog-style value ordering of numbers is intended (as the comments claim): remove
  numeric kinds from the `kind_order` gate and keep a deterministic tie-break
  (e.g. `Int < Date < Real` on exact value ties).
Companion report §4 covers how both options relate to the C++ order (including the
list-compares-length-first divergence, which deserves the same deliberate decision).

### B6. `normalize_term` panics (index out of bounds) on excess positional arguments
`oper.rs:649-690` (crash at `oper.rs:677`).

`xs` is sized to the *definition's* arg count, but the loop indexes `xs[i]` with `i` ranging
over the *term's* args:

```text
defs:  [op(box(wd,ht),fun,0,none)]
input: box(1,2,3).
PROBE: thread panicked at arena-terms/src/oper.rs:677:38:
       index out of bounds: the len is 2 but the index is 2
```

**[probe-confirmed]** A malformed *input document* must produce a parse error (the C++
`arrangeArgs` says "too many arguments"), never a panic — this is a DoS on any service that
parses untrusted `.ax` input.

* **Fix:** bounds-check before both `xs[i]` uses and `bail!("too many arguments in {name}")`.
* While in there: reconsider the positional-fill strategy (Rust pins positional extras to
  their own index; C++ fills the first free slot — legacy inputs mixing named-then-
  positional args parse in C++ and error in Rust). See companion report §8.

### B7. String interpolation without a defined `++` panics via `assert!`
`lexer.rs:350-372, 1036-1052` + `parser.rs:196`.

The lexer emits an `AtomOper("++")` token with `op_tab_index = arena.lookup_oper("++")`.
With a plain `Arena::new()` (default opers are opt-in via `try_with_default_opers`),
that index is `None`, and the first precedence conflict hits:

```text
input: "a{1}b" .
PROBE: thread panicked at arena-terms-parser/src/parser.rs:196:9:
       assertion failed: op_tab1.is_oper()
```

**[probe-confirmed]** Library code driven by user input should not `assert!` — return a
`ParlexError` ("operator `++` is not defined; string interpolation requires it"), or better,
have `TermParser::try_new`/`TermLexer::try_new` ensure the two structural operators (`++`,
prefix `-`) exist, as the legacy parser constructor did.

### B8. `Display` of an out-of-range date panics inside `chrono`
`display.rs:102-114` (`DateTime::from_timestamp(...).unwrap()`).

```rust
Term::date(i64::MAX).display(&a)   // PROBE: panics (from_timestamp returned None)
```

**[probe-confirmed]** `chrono` supports roughly ±262,000 years; anything outside → `None` →
`unwrap` panic. The parser happily constructs such dates (`date{9300000000000000000}` is
within i64), so parse-then-print panics. Fall back to printing the raw epoch form
`date{<ms>}` when `from_timestamp` fails (the lexer already accepts it — nice symmetry).

### B9. `Eq`/`Ord` for `View` violate their contracts on float edge cases
`view.rs:188-196` (`a == b` on f64) vs `view.rs:258-266` (`total_cmp`).

* `View::Real(NaN)`: `eq` → `false` (so `x != x`, breaking `Eq`'s reflexivity — the marker
  `impl Eq for View` at `view.rs:242` is a false promise), while `cmp` → `Equal`.
* `0.0` vs `-0.0`: `eq` → `true`, `cmp` (total order) → `Less`.

Either use `total_cmp`-semantics in `eq` too (`a.total_cmp(&b) == Equal`) — consistent, and
NaN becomes self-equal like `Ord` already claims — or drop the `Eq` impl. Implementing
`PartialEq` via `cmp` (B3 fix) resolves this automatically.

### B10. Displayed atoms don't escape backslashes/control characters → round-trip breakage
`display.rs:67-74`.

`write_atom_str` escapes only `'`. An atom named `a\b` prints as `'a\b'`, which the lexer
reads back as `a` + backspace (`StrAtomCharBackspace`). Newlines, `\x..`-worthy control
bytes, etc. all round-trip wrong. Strings get full escaping (`write_str_quoted`,
`display.rs:76-100`); atoms need the same table (share the helper). The legacy printer
escaped quoted atoms byte-by-byte via `termwtab` — parity requires it too.

### B11. `listc`/`list![…; tail]` silently drop the tail when the element list is empty
`term.rs:371-391` (and macro arm `term.rs:781-786`).

`Term::listc(arena, [], tail)` returns `Term::NIL`, discarding `tail`. The legacy
`makeList(begin,end,tail)` had the same quirk, but in Rust it's an easy silent data-loss
footgun (`list![; t]` compiles). Either return `tail` itself (the Prolog-consistent
reading of `[|T] ≡ T`), or make the empty-with-tail case an error/`debug_assert`, and
document whichever you choose.

### B12. `list!` macro is unhygienic: bare `Term` type annotation
`term.rs:783`.

```rust
let __tail: Term = $tail.into_term(__arena);
```

Every other reference in the macros uses `$crate::Term`; this one requires `Term` to be
imported at the *call site* — `list![1, 2; tail]` fails to compile in a module that only
`use arena_terms::{list, IntoTerm}`. Change to `$crate::Term` (and add a compile test that
invokes each macro in a scope with no imports).

### B13. `#[derive(Default)]` on `Arena` bypasses random IDs
`arena.rs:51`.

`Arena::default()` produces `arena_id = 0`, `epoch_ids = [0; 8]` — *every* defaulted arena
shares identity, so handles from one validate against another (the exact confusion the
random IDs exist to prevent), and `Default` disagrees with `new()`. Implement `Default`
manually as `Self::new()`.

### B14. `Slice` index/len are `u32` with unchecked `as` casts
`arena.rs:601-682` (`index as u32`, `len as u32`).

An arena that grows past 4 GiB of bytes (or 2^32 terms — 64 GiB, less likely) silently
wraps, producing handles that point at the wrong data while still passing epoch-range
verification. Given the crate targets "large-scale term manipulation", either
`u32::try_from(...).expect("arena exceeds u32 index space")` (fail loud) or widen to
`u64`/`usize` (the enum stays 16 bytes only with u32×2 + epoch — so failing loud is the
cheap correct option).

---

## C. API design observations

1. **`Term`'s derived `PartialEq`/`PartialOrd` are exposed and misleading**
   (`term.rs:72`). They compare handles: `AtomRef` vs `Atom` of the same name are unequal;
   ordering is by enum discriminant then payload bits. The `TODO` at `term.rs:67-71`
   already doubts this. Recommendation: keep a *private* handle comparison for internal
   use (`is_list`'s `*self == Self::NIL` etc.), expose `Term::same_handle(&self, other)`
   if needed, and remove/replace public `PartialEq`/`PartialOrd` (or document loudly).
   Note `is_list`/`is_tuple` treating the atoms `nil`/`unit` as list/tuple is a semantic
   aliasing worth a doc note (companion report §1.2).

2. **`ArenaID` is dead weight.** It's generated, stored, printed in `Debug` — and never
   checked anywhere (`Slice` carries only `epoch_id`; grep confirms no verification reads
   `arena_id`). Cross-arena safety is purely probabilistic via random u32 epoch IDs
   (~1/4·10⁹ per stale-epoch pair), yet `CLAUDE.md` and doc comments say "runtime-checked
   via ArenaID". Either check it (would require widening `Slice` or hashing arena_id into
   epoch ids) or delete the field and fix the docs.

3. **`unpack_atom(term, &[])` sentinel.** Empty-slice-means-any is stringly control
   coupling; you already have `atom_name()` for the unfiltered case. Consider
   `unpack_atom(term)` + `unpack_atom_in(term, names)`, or accept
   `impl IntoIterator<Item=&str>` and treat `None` distinctly.

4. **`IntoTerm for FnOnce(&mut Arena) -> Term`** (`term.rs:194-202`) is clever but is the
   direct enabler of B1, and blanket-closure impls make type-inference errors cryptic.
   After the two-phase fix it's safe; still worth documenting the evaluation order.

5. **`Arena::int/real/date/term` take `&mut self` needlessly** (`arena.rs:239-263`) and
   `pub fn term<'a, T: IntoTerm>(&'a mut self, …)` declares an unused lifetime. The
   uniformity argument is fine — then say so in a comment; otherwise make them `&self` (or
   free `Term::int` only, which already exists).

6. **`TermTokenParser` vs `TermParser`** (`parser.rs:766, 936`): the token-yielding one and
   the term-yielding one differ by ~40 lines of near-duplicated 70-line doc comments. The
   names don't telegraph the difference (`TermParser` yields `Term`; `TermTokenParser`
   yields `TermToken`). Consider `TermParser` + `TermParser::tokens()` adapter, or at least
   deduplicate the docs (see also F3 — the docs reference nonexistent types).

7. **`get_oper(None | out-of-range) -> &EMPTY_OPER_DEF_TAB`** (`oper.rs:369-377`)
   silently maps bugs (a stale index) to "no operator". Fine for `None`; for
   `Some(out_of_range)` a `debug_assert!` would catch table/arena mixups.

8. **Errors**: `TermError::OperDef(String)` and `::Encoding(String)` are stringly variants;
   fine for now, but `bail!` (`oper.rs:31-35`) does `String::from(format!(…))` — a
   `smartstring` copy of a `std::String`; make the macro build the target type directly.
   Also `error.rs:10` still says *"errors that can occur within the calculator"* — a
   copy-paste from the parlex calculator example.

---

## D. File-by-file — `arena-terms`

### `lib.rs`
* `pub(crate) use term::{Handle, Slice, TinyArray};` — `TinyArray` re-export is unused
  (clippy). Drop it.
* Crate doc says equality/ordering follow "Prolog's standard order of terms" — after
  B3–B5/§4-of-companion fixes, revisit this claim (esp. list length-first ordering).

### `error.rs`
* Calculator copy-paste in the doc (§C8). Doc for `InvalidTerm` could explain the usual
  cause (stale epoch / wrong arena) — it's the error users will actually hit.
* `InternalTermError` is fine; note both variants are converted to
  `TermError::InvalidTerm` at every use site (`view.rs`), so the distinction is currently
  cosmetic.

### `term.rs`
* B1 (lazy iterator hazard), B11, B12 above; `arity()` underflow: `FuncRef(Slice{len: 0})`
  would wrap (`(n - 1) as usize`, `term.rs:625`) — unreachable via public API today, but a
  `debug_assert!(n >= 1)` documents the invariant.
* `From<u8..u32,i8..i64,f32,f64> for Term` but no `TryFrom<u64/usize>` — fine; consider
  documenting why (silent wrap avoidance) next to the macro.
* Macros: `func!` requires ≥1 arg while `Term::func` accepts 0 (returns atom) —
  inconsistent surface; `atom!("x")` covers it, but a `func!["foo";]` arm would be cheap.
  `date!`/`unit!`/`nil!` exist but no `int!`/`real!` — either prune `date!` or complete the
  set (smell: partial macro family).
* Doc example on `Debug` (`term.rs:687-691`) is good; note `Var` debug prints
  `<invalid utf8>` fallback that can't occur (constructors enforce UTF-8) — harmless.
* Tests: heavy `dbg!` output left in (`compound_construction_and_formatting`,
  `view_construction`, `interface`, …) — makes `cargo test -- --nocapture` unusable;
  `assert!(x == y)` instead of `assert_eq!` in several places; `#[should_panic]` tests
  (`stale_term_str` etc.) lack `expected = "…"` so *any* panic passes — with B2 fixed these
  should assert the specific error instead of panicking via `unwrap`.

### `arena.rs`
* B1, B2, B13, B14 above.
* `epoch_index` is O(K) linear scan per view — K ≤ 8 so fine; a comment noting the bound
  keeps future readers from "optimizing" it.
* `unpack_func`/`unpack_tuple`: `return Ok((functor, arr));` / `return Ok(arr);` — trailing
  `return` (clippy `needless_return`, 4×).
* `name()` (`arena.rs:365-374`): `Ok(functor.atom_name(ar)?)` → just
  `functor.atom_name(ar)`.
* `unpack_list` returns `(&[], &Term::NIL)` via const-promotion — fine, but worth a
  comment; the `View::Atom(_) if term == &Term::NIL` guard relies on handle equality
  (OK: `nil` is always inline).
* Doc comment on `truncate` says "Epoch `m` and all epochs more recent than `m` are
  erased" — after the B2 fix, also state that the epoch *ID* changes (handles die).

### `view.rs`
* B3, B4, B5, B9 above.
* The three `cmp` compound arms are triplicated 15-line loops (`view.rs:288-338`); factor a
  `fn cmp_args(arena_a, xs, arena_b, ys) -> Ordering`.
* `expect("arena mismatch")` inside `eq`/`cmp` (`view.rs:214, 223-226, 283, …`): panicking
  in comparison operators is hostile — a stale term in a sorted collection brings the
  process down. Since you can't return `Result` from `Ord`, either document prominently or
  make `view()`-failure compare as a distinct extreme (both are defensible; pick one).
* `unsafe { from_utf8_unchecked(...) }` ×6: the invariant ("bytes written by intern_str are
  valid UTF-8 and slices are never re-spliced") should be stated in a `// SAFETY:` comment
  at each site (currently none) — and it is *not actually upheld* until B2 is fixed. Until
  then, `from_utf8` + `map_err` costs one scan and removes UB risk; measure before keeping
  `unchecked`.
* `ListCRef` view computes `let last = slice.len() - 1;` (`view.rs:156`) — guaranteed ≥ 2
  by the constructor; another candidate for `debug_assert`.

### `oper.rs`
* B6 above; plus the duplicated precedence-range check (`oper.rs:425-432` and `487-496`) —
  the second is unreachable (first one already bailed); delete one.
* `#[cfg(false)]` block (`oper.rs:508-518`): works (stabilized boolean cfg), but a
  `#[cfg(feature = "strict-operdefs")]` or a plain comment would be more discoverable than
  compile-time-disabled code with no test.
* `define_opers` (`oper.rs:579-590`): `ts.to_vec()` clones the slice to appease the borrow
  checker — fine, but note it also **silently ignores an improper list's tail**; a
  malformed defs term `[op(...) | Junk]` half-succeeds. Bail on non-NIL tails.
* `OperDefTab::new()` is `const` but clippy asks for `Default` too — derive-able via
  `impl Default { fn default() { Self::new() } }` (clippy `new_without_default`).
* `Fixity::STRS: &[&str]` could be `[&str; Self::COUNT]` so the
  `assert_eq!(STRS.len(), COUNT)` tests become compile-time facts.
* `From<Fixity> for String` + `Display` + `TryFrom<&str>` + `TryFrom<String>` + `FromStr`
  ×2 enums = 10 conversion impls of boilerplate; a tiny macro or `strum` would halve the
  file. [taste]
* `normalize_term`: on `embed_fixity` it allocates `self.atom(String::from(fixity))` per
  call — `self.atom(fixity.as_str())` (add an `as_str()` returning the `STRS` entry) avoids
  the `String`.
* `unique_arg_names: HashSet<_> = args.iter().map(|x| &x.name).cloned()` —
  `map(|x| x.name.as_str())` borrows fine and skips clones.

### `display.rs`
* B8, B10 above.
* `write_str_quoted` builds an intermediate `String` and does `out.push_str(&format!(…))`
  per control char (`display.rs:76-100`); write straight to the formatter
  (`f.write_str`/`write!`) — that's what `fmt::Formatter` is for.
* `Real` branch: `write!(f, "{}", r)` prints `NaN`/`inf` (documented unparseable — OK), but
  also loses the `{:.1}` normalization for e.g. `1e300` (prints hundreds of digits). If the
  goal is "always re-parseable and short", consider `ryu`-style shortest with a forced
  `.0`/exponent — or accept and document.
* Errors are mapped to `fmt::Error` (`display.rs:63,126`) — `format!` **panics** on that
  ("a formatting trait implementation returned an error"). So displaying a stale term
  panics with an unrelated message. Consider printing `<invalid term: …>` instead; Display
  impls should be infallible in practice.
* `View::Func` with empty args prints `/* invalid Func */` (`display.rs:148-150`) — can't
  happen via constructors; make it `debug_assert!` + fall through, or keep but add a test.

### `encoding.rs`
* Alias asymmetry in `from_name`: `"latin1"`/`"l1"`/`"iso-8859-1"` (special-cased) →
  `Iso8859_1` (true Latin-1), but other IANA aliases of the same encoding that fall through
  to `encoding_rs::for_label` (`"cp819"`, `"iso8859-1"`, `"iso_8859-1:1987"`, …) →
  `Windows1252`. Two spellings of the same charset name silently select different
  decoders. Extend the special-case list to all WHATWG labels of windows-1252 that
  *lexically* say 8859-1, or document the exact accepted spellings.
* `to_encoding_rs`: the `Ascii | Iso8859_1 => WINDOWS_1252` arms (`encoding.rs:160`) are
  unreachable (both are special-cased in `decode`/`encode` before delegation) — misleading;
  make them `unreachable!()` or restructure so the special-casing lives in one place.
* ASCII decode uses `unsafe { String::from_utf8_unchecked(...) }` (`encoding.rs:268`) right
  after a full scan — `from_utf8(...).unwrap()` costs the same scan it already did and
  drops the `unsafe`. Not worth an unsafe block.
* UTF-16 decode via `encoding_rs::Encoding::decode` does BOM sniffing (a UTF-16LE stream
  with a BE BOM will switch encodings); if that's not desired use
  `decode_without_bom_handling`.
* `Encoding::ALL` formatting is why `cargo fmt --check` fails — add `#[rustfmt::skip]` if
  the grouped layout is intentional (it is nice), otherwise let rustfmt have it.

---

## E. File-by-file — `arena-terms-parser`

### `lib.rs`
* Doc "# Modules" lists `oper` which no longer lives here (moved to arena-terms in 0.4.0).

### `build.rs`
* Four `cargo:warning=` lines print on **every** build of every dependent (`build.rs:48-62`)
  — warnings are for problems; use plain `println!` logging only when debugging, or drop.
* `generate(...).unwrap()` twice — `expect("alex generation failed for src/term.alex")`
  gives actionable build errors.

### `token.rs`
* `merge_span` uses nested `match` where `if let`/`Option::map` reads better
  (clippy single-pattern match). `Value` derives `Copy`, yet call sites `.clone()` it 24
  times (clippy `clone_on_copy`) — mechanical cleanup.

### `term.alex` / `termx.g`
* Solid, readable specs. `HA` (12-hour) admits `00` which `%I` rejects — `date{06/16/1799
  00:30 AM}` errors at chrono-parse time with a lexer-span error; acceptable, but a note in
  the spec would help.
* `termx.g` `term4: Term -> .` accepts a lone `.` as an empty statement (parity with legacy
  lexer trickery) — good; covered by test `one_term`.

### `lexer.rs`
* B7 above (also the hardcoded `"++"` lookups at `lexer.rs:356`, `1043`).
* Dead leftovers: `if &s[s.len() - 1..] == "\n" { }` with an empty body (`lexer.rs:604-606`
  — and after `trim()` the condition can't even be true), `if lexer.buffer[0] != b':' { }`
  (`lexer.rs:706-708`), several `// New line` no-op arms. Each is a small "did I forget
  something?" trap for readers; delete or comment *why* nothing happens.
* Buffer surgery relies on DFA-guaranteed shapes (`lexer.buffer[len-2]`,
  `s.drain(0..5)`, `truncate(len-3)`, `Time6`'s `len-3` slicing, …). All correct as far as
  I can trace, but one changed regex breaks them silently. Consider tiny helpers
  (`strip_suffix_bytes(n)`, `strip_prefix_bytes(n)`) with `debug_assert!`s, so a mismatch
  panics in tests rather than corrupting data.
* `take_str` (`lexer.rs:230-238`): `Vec<u8>` → `decode` → `std::String` → smartstring
  `String::from(s)` — for > 23-byte tokens that's two copies (three with UTF-8: `decode`'s
  `to_owned`). For the hot path (UTF-8) a borrow-based route
  (`str::from_utf8(&bytes)` → `arena.atom(s)`) avoids both; worth it only if profiling
  agrees, but the `Encoding::Utf8 → s.to_owned()` copy inside `decode` is avoidable today
  (return `Cow`).
* `format!` with no interpolation ×7 (clippy `useless_format`), e.g. `lexer.rs:368, 779`.
* `Rule::Empty => unreachable!()` — fine, but a comment (generated sentinel) helps.
* Tests are excellent (dates matrix, CRLF semantics with legacy-parity comments, heredocs).
  Same `dbg!` noise complaint as the core crate.

### `parser.rs`
* B7 above (`assert!(op_tab1.is_oper())`, `parser.rs:196`); the two `panic!("expected
  shift/reduce")` on `parser.rs:143-149` are table invariants — `debug_assert!`-grade, or
  return `ParlexError` (generated tables could in principle change shape).
* `resolve_ambiguity`: the `min_prec2`/`max_prec2` construction defaulting missing fixities
  to `MAX_OPER_PREC`/`MIN_OPER_PREC` respectively is subtle — when only one of
  infix/postfix exists, min==max==its prec, good; when neither, min > max, and the final
  `else` errors — add a comment, it took real effort to verify.
* `reduce`: consistent and readable. `ProdID::Tuple`'s unary-unwrap carries a good comment.
  One perf nit: `let xs = [oper, expr1, expr2]; xs.iter().chain(...)` then `funcv(vs)` —
  fine; but `funcv` re-checks the functor is an atom on every operator reduction — micro,
  skip.
* Stale doc references: `TermParserError`, `LexerError<I::Error, CalcError>`, `CalcToken`,
  `[`ParserError<…CalcError…>`]` (`parser.rs:743-746`, `912-916`) — none of these types
  exist in the workspace; copy-paste from the parlex calculator example. Same for
  `token.rs` header mentioning "calculator". Doc-only, but it's user-facing on docs.rs.
* `TermParser::try_next_with_context` maps `Value::Index` to an error (`parser.rs:1002`) —
  correct; message `"index token not expected"` could name the production for debugging.

### `main.rs`
* `dbg!(&parser.stats()); dbg!(&token);` inside the parse loop (`main.rs:110-111`) — the
  CLI prints internal debug spew to stderr for every term; gate behind `log::debug!`.
* `Arena::try_with_default_opers().unwrap()` (`main.rs:98`) — `?` with a decent message;
  `token.span().unwrap()` (`main.rs:112`) can be `unwrap_or_default()` to keep the CLI
  panic-free.
* `Sizes {}` unit-struct variant with braces; drop the braces. The whole subcommand is a
  dev tool — fine, but consider hiding it from `--help` (`#[command(hide = true)]`).

---

## F. Tooling & hygiene

1. **`cargo clippy --all-targets` fails**: `clippy::approx_constant` (deny-by-default) on
   `3.14` in `term.rs:1109` (test). Change the test constant (e.g. `3.5`) — done in other
   tests already (`unpack_primitives_ok` uses 3.5).
2. **~100 clippy warnings** (lib + tests). Breakdown: 32 needless borrows for generic args
   (mostly `&[Term]` literals in tests), 24 `clone()` on `Copy` `Value`, 8 needless
   ref-deref, 7 `useless_format`, 4 `needless_return`, 3 single-pattern `match`, 3
   elidable lifetimes, 2 `nonminimal_bool`, 2 manual range-contains
   (`prec < MIN || prec > MAX` → `!(MIN..=MAX).contains(&prec)`), 1 each: missing
   `Default` for `OperDefTab`, useless `String` conversion, unused import (`TinyArray` in
   `lib.rs`), `into_iter` on slice (`oper.rs:438`), `op_ref`, `to_*` taking `&self` on
   `Copy` type (`to_encoding_rs`), empty line after doc comment, empty doc comment
   (`token.rs:86`). Nearly all are `cargo clippy --fix`-able; consider then adding
   `#![warn(clippy::all)]` + CI gate so they don't regrow.
3. **`cargo fmt --check` fails** (at least `encoding.rs::ALL`). Decide: `#[rustfmt::skip]`
   or reformat — but make the check pass, since `CLAUDE.md` advertises it as a project
   command.
4. **No integration-test dirs** are shipped (`tests/` empty in both crates) — all tests are
   unit tests in-file (fine), but public-API-only compile tests (e.g. macro hygiene, B12)
   belong in `tests/`.
5. **Docs**: several rustdoc links (`[`LexerCtx`]`, `[`TermParseError`]`,
   `[`OperDefs`]: crate::oper::OperDefs` in the parser crate) are dangling — `cargo doc`
   warns; `#![warn(rustdoc::broken_intra_doc_links)]` would surface them.
6. **`x.ax` untracked at repo root** (git status) — test junk? Add to `.gitignore` or
   commit intentionally.

---

## G. Prioritized recommendations

**P0 — correctness, fix before anything else**
1. Two-phase arg collection in `intern_func`/`intern_seq`/`intern_seq_plus_one` (B1).
2. Regenerate epoch ID in `truncate` (B2) — closes the `from_utf8_unchecked` UB path.
3. Bounds-check in `normalize_term`; error instead of panic (B6).
4. Replace `assert!(op_tab1.is_oper())` with an error; auto-define `++`/`-` in
   `TermParser::try_new` or fail soft (B7).

**P1 — contract violations & round-trip bugs**
5. Rewrite `View` `eq`/`cmp`: functor-by-view, exact `i64` compares, one consistent
   numeric/kind policy, `PartialEq` delegated to `cmp` (B3, B4, B5, B9).
6. Escape atoms fully in display (B10); fall back to `date{<ms>}` on chrono overflow (B8).
7. `$crate::Term` in `list!` (B12); decide `listc([], tail)` semantics (B11);
   manual `Default` for `Arena` (B13); checked `u32` casts in `intern_*` (B14).

**P2 — API polish**
8. Atom/var interning in the arena (fixes B3's root cause, memory growth, and restores
   C++-parity handle equality).
9. Retire or rename `Term`'s public `PartialEq/PartialOrd`; resolve the `ArenaID` docs-vs-
   reality question.
10. Deduplicate `TermParser`/`TermTokenParser` docs; purge calculator remnants.

**P3 — hygiene**
11. `cargo clippy --fix`, fix the deny, make `cargo fmt --check` pass, remove `dbg!` from
    tests/CLI, delete dead lexer branches, `SAFETY:` comments on every `unsafe`.
