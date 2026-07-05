# Review: Logical gaps between `arena-terms`/`arena-terms-parser` (Rust) and the C++ terms implementation

**Reviewer:** Claude (Fable 5) — 2026-07-05
**Rust side:** `arena-terms` + `arena-terms-parser` v0.6.2 (workspace @ `~/gproj/arena-terms`)
**C++ side:** `~/gproj/tptools-instrument/utils` — `terms.h`, `awrterms.hpp`, `awrterms.cc`,
`lexer.l`, `term.g`, `term.htab`, `parser.h`, `parser.cc`, `unify.cc`, `term_utils.h`
(plus `test.ax` / `rdl.ax` as syntax witnesses).

**Method.** Every file above was read in full on both sides. Where behavior was in doubt I
compiled and ran probe tests against the Rust crates (all shipped tests pass: 137/137).
Divergences already documented in `arena-terms-parser/README.md` / `CHANGELOG.md`
("Known Divergences from Legacy": `123e5` floats, Excel dates → epoch-ms dates) are listed
only briefly in §10.

Severity legend: **[H]** functional gap likely to matter, **[M]** divergence users can hit,
**[L]** minor/cosmetic, **[✓]** parity confirmed, **[+]** Rust improvement over C++.

---

## 0. Executive summary

| # | Area | Gap | Sev |
|---|------|-----|-----|
| 1 | Data model | No term **annotations** (`_AX_ANNOTLIST`, `annot`/`annotate`, parser source-info) | H |
| 2 | Data model | `NIL`/`UNIT` are atoms `nil`/`unit` vs C++ `'[]'`/`'()'` — breaks cross-system text round-trip | H |
| 3 | Memory | No atom/var **interning (dedup)**; C++ hash-dedups atoms & vars | H |
| 4 | Memory | 8 LIFO epochs vs 64 random-access regions + persistent atom region + `markRegion`/`clearRegion(mark)` | M |
| 5 | API | All 10 `to*` **type conversions** missing (`toAtom`, `toString`, `toList`, …) | M |
| 6 | API | `Env` + `unify`/`bind`/`deref` missing entirely | M |
| 7 | API | `isGround`, `copy` (cross-arena), fresh-var generator `makeVar()` missing | M |
| 8 | Ordering | Standard order of terms differs from C++ (kind order, list/func comparison strategy) | H |
| 9 | Printer | No printer options (bin/hex mode, string mode, real precision); `bin{N:…}` output form gone | M |
| 10 | Printer | Atom quoting/escaping diverges (operators quoted, controls not escaped, `[]`/`()` not special-cased) | M |
| 11 | Operators | `op/4` accepted only via parser normalization; `define_oper` API needs `op/6` | M |
| 12 | Operators | Different **default operator set** and defaults are opt-in (`try_with_default_opers`); interpolation breaks without `++` | H |
| 13 | Operators | `arrangeArgs` vs `normalize_term`: positional-after-named fill strategy differs; error vs **panic** on excess args | H |
| 14 | Dates | `date{…}` output of each system is not readable by the other (semantic + format change) | M |
| 15 | Misc | `show(fmt)`, byte-level `first`/`rest`/`at`/`size`/`data`, `term_utils` helpers missing | L |

Items 8, 12, 13 overlap with outright Rust bugs; those are detailed with probe evidence in
`fable5-review-arena-idiomatic-rust.md` and only summarized here.

---

## 1. Core data model (`terms.h`, `awrterms.hpp` ↔ `term.rs`, `arena.rs`)

### 1.1 Handle layout — informational, no action
C++ `Term` is a NaN-boxed 8-byte union (`terms.h:52-241`): reals sacrifice the mantissa LSB
(`realflag`), dates sacrifice the low 8 mantissa bits, ints are 32-bit, inline payloads are
≤ 6 bytes, out-of-line data is addressed by `region:7 / size:16 / addr:32` with multi-chunk
chaining for > 64 KB payloads. Rust `Term` is a 16-byte tagged enum (`term.rs:40-56`) with
full `i64`/`f64` payloads and ≤ 14-byte inline strings. This is a deliberate redesign;
consequences worth calling out:

* **[+]** Rust reals/dates/ints are exact (no stolen mantissa bits, no `adjustNaN`, 64-bit ints).
* **[+]** No 64 KB chunk limit, no chunk-walking loops.
* **[M]** Binary interop with C++ heaps (e.g. `Heap::data()` of a compound returning the raw
  `Term[]` bytes, `dump8` diagnostics) has no equivalent — see §7.4. If any persisted data
  used the C++ 8-byte layout, there is no reader on the Rust side.

### 1.2 `NIL` / `UNIT` naming — **[H]**
C++: `NIL` is the atom `'[]'`, `UNIT` is the atom `'()'` (`awrterms.cc:108-109`); the
printer special-cases both as unquoted (`needQuotes`, `awrterms.cc:1089`), so an empty list
prints as `[]` and re-parses as the empty list *in both systems*.
Rust: `Term::NIL` is atom `"nil"`, `Term::UNIT` is atom `"unit"` (`term.rs:409-420`), and
display prints `nil` / `unit` (`display.rs:167-179` never sees an empty `View::List`).

Internally each system is self-consistent, but **text produced by one is misread by the
other**: Rust `nil` parses in C++ as the ordinary atom `nil` (not the empty list), and C++
`[]` parses in Rust fine, but a C++ atom `'()'`/`'[]'` embedded in data becomes `unit`-like
only on the C++ side. Also, on the Rust side the ordinary atoms `nil`/`unit` are now
indistinguishable from the empty list/tuple (C++ had the same aliasing, just with `'[]'`/
`'()'`, which are far less likely to appear as user atoms than `nil`).
*Recommendation:* if cross-compat matters, print `[]`/`()` for `NIL`/`UNIT` (parse already
accepts them), or at least document the aliasing of the plain atoms `nil`/`unit`.

### 1.3 Sentinels and empty-value constants — **[M]/[+]**
C++ exports `NaT`, `FNIL`, `SNIL`, `BNIL`, `ANIL`, `VNIL`, `ATOM_NULL`, `ATOM_CONS`,
`ATOM_TUPLE`, `ATOM_EQUAL`, `ATOM_MINUS`, `ATOM_CONCAT`, `ATOM_OP`, `ATOM_DOT`
(`awrterms.hpp:72-87`). Rust has only `NIL`/`UNIT`.

* `NaT` → `Option<Term>`/`Result` — **[+]** better, nothing to do.
* `FNIL` (arity-0 func distinct from its atom): C++ can *represent* `f()` (`vMakeFunc` with
  `arity==0` produces `AX_FUNC` of length 1) even though the grammar can't parse it. Rust
  collapses zero-arg funcs to the atom (`Term::func` doc, `term.rs:311`). **[L]** — fine,
  but it is a representable-value difference; document it.
* The `ATOM_*` handles are used in C++ for fast handle-equality checks (e.g. printer's
  `'++'` special case, `cons`). Rust equivalents are ad-hoc string compares. **[L]**.

### 1.4 Annotations — **[H] biggest single feature gap**
C++ supports transparent term annotation: `_AX_ANNOTLIST` wraps `(term, annotList)` and
*every* accessor (`type`, `integer`, `at`, `length`, `eq`, `compare`, conversions…)
dereferences it automatically (`awrterms.hpp:449-504`, `awrterms.cc:895-919`). The parser
uses it for provenance: with `sourceInfoFlag`, every token and every reduced term is
annotated with `source(streamName, lineNo)` (`parser.h:172-177`, `parser.cc:473-510`).

Rust has no annotation mechanism at all. Token `Span`s exist in the parser, but
`TermParser::try_next_with_context` returns a bare `Term` and the span is dropped
(`parser.rs:997-1011`); nothing survives into the term graph. Any downstream tooling that
relied on `annot()` to report "error at file:line for this subterm" cannot be ported.
*Recommendation:* either an arena-side sidecar map (`Term`-slice-id → annotation `Term`) or
an `AnnotRef` handle variant mirroring `_AX_ANNOTLIST`. This needs to be designed into the
arena; retrofitting later will be harder.

---

## 2. Memory management (`Heap` regions ↔ `Arena` epochs)

### 2.1 Region model — **[M]**
C++ `Heap` has **64 independent regions** with `switchRegion(reg)`, per-region
`markRegion()`/`clearRegion(mark)` (arbitrary rollback points, not just region boundaries),
and a dedicated hashed region (`MAX_REGIONS-1`) where atoms/vars/stream-names "stick
forever" (`awrterms.hpp:203-240`, `parser.h:120-127`). The printer allocates temporaries
and rolls them back per `_print` call (`awrterms.cc:1143,1287`).

Rust `Arena` has **8 strictly-LIFO epochs** (`arena.rs:90`), and `truncate` kills
*everything* from the target epoch up — including atoms interned there. Consequences:

* No equivalent of "persistent atom region + scratch regions": in Rust, a long-lived atom
  interned during a scratch epoch dies with it. Callers must plan to intern long-lived
  atoms in epoch 0 *before* starting scratch epochs.
* No sub-epoch rollback (`markRegion`/`clearRegion(mark)`); mitigated by cheap
  `begin_epoch`, but the 8-epoch cap makes nesting shallow. `MAX_LIVE_EPOCHS = 8` vs 64
  regions; a recursive printer/evaluator that nests scopes > 7 deep errors out.

Not necessarily wrong — the LIFO model is simpler and safer — but the gap should be a
documented, conscious decision. (Also note `truncate` currently has a stale-handle-aliasing
bug; see the idiomatic-Rust report, finding **B2**.)

### 2.2 Atom/variable interning — **[H]**
C++ dedups every atom and var through `HashTab::insert` with move-to-front chains
(`awrterms.cc:1380-1446`); the same name always yields the same handle, so handle equality
is name equality, and memory does not grow with repetition.
Rust `intern_str`/`intern_bytes` (`arena.rs:601-623`) **never dedup** — the "intern"
terminology is misleading. Every occurrence of an atom > 14 bytes appends a fresh copy:

* Parsing a large file that repeats a long functor N times stores N copies (C++ stores 1).
* Handle equality for long atoms is lost, which is exactly what makes the `View`
  functor-equality bug possible (idiomatic report **B3**).

*Recommendation:* add a per-arena (or per-epoch-aware) hash map for `AtomRef`/`VarRef`
interning. Strings/binaries can stay un-deduped (C++ doesn't dedup them either).

### 2.3 Fresh variables — **[L]**
C++ `makeVar()` generates `_G<seq>` names (`awrterms.hpp:274-278`). No Rust equivalent;
needed by any future unification port.

---

## 3. Term access API (`Heap` accessors ↔ `Term`/`Arena`/`View`)

| C++ | Rust | Status |
|-----|------|--------|
| `type(t)` / `typeName` | `kind_name`, `is_*` predicates | ✓ |
| `integer/real/date` | `unpack_int/real/date` | ✓ |
| `functor/arity/arg` | `unpack_func*`, `arity`, `name` | ✓ |
| `head/tail` (lists) | `unpack_list` → `(&[Term], &Term)` | ✓ (slice-based, better) |
| `cons(t, ts)` | — (`listc` builds many-at-once) | [L] no single-cons helper |
| `at(t, i)` random access | slice indexing | ✓ |
| `length`, `listLength` | slice `.len()` | ✓ |
| `first/rest` on **atoms/strings/binaries** (byte car/cdr, `awrterms.cc:759-833`) | — | [L] niche; `unpack_str/bin` slices cover it |
| `size(t)` (byte size), `data(t)`/`data(t,buf)` raw bytes (incl. compounds!) | — | [L]/[M] see §7.4 |
| `show(t, fmt)` printf-style per-value formatting (`awrterms.cc:266-295`) | — | [M] no formatted scalar output |
| `getString(t)` | `term.display(&arena).to_string()` | ✓ |
| `isAtomic/isNumber/isCompound` | `is_number` only | [L] add `is_atomic`/`is_compound` |
| `isFunc(t, name, arity)` / `isAtom(t, name)` | `unpack_func(a, &["name"])` etc. | ✓ (richer) |
| `isGround(t)` (`awrterms.cc:496-520`) | — | [M] missing |
| `toInteger/toReal/toDate/toAtom/toVar/toString/toBinary/toFunc/toList/toTuple` (`awrterms.cc:297-491`) | — | [M] see §3.1 |
| `Heap::copy(h, t)` cross-heap copy (print→parse hack, `awrterms.cc:1009-1015`) | — | [M] see §3.2 |

### 3.1 Type conversions — **[M]**
The C++ `to*` family is O(1) — it just retags the handle (`((_Term*)&t)->all.type = …`) and
the payload is reinterpreted, with numeric conversions where needed (`toInteger(real)`
truncates, `toInteger(atom)` = `atoi`, etc.). In the Rust model the same O(1) retag is
trivially expressible (`Handle::Str(x)` → `Handle::Atom(x)`, `StrRef` → `AtomRef` — same
`TinyArray`/`Slice` payload) but there is **no API for any of it**. Porting C++ call sites
(`toList` in `isGround`/`eq`/`compare` style iteration, `toString`/`toAtom` in data
munging) is currently impossible without re-interning through `&str`.
*Recommendation:* add `Arena::{to_atom, to_var, to_str, to_bin}` (retag) and
`{to_int, to_real, to_date}` (numeric/string parse), plus `to_func/to_list/to_tuple` for
compound retagging (note: Rust funcs store the functor in slot 0, so `to_list(func)` should
decide whether the functor is included — C++ includes it).

### 3.2 Cross-arena copy — **[M]**
C++ at least has the "sloppy" print→parse `copy`. Rust `Term`s from arena A cannot be
viewed against arena B (by design), and there is no copy/migrate API at all. Any multi-arena
architecture (per-request arenas feeding a long-lived cache arena) is blocked.
*Recommendation:* implement a real recursive `Arena::copy_from(&mut self, other: &Arena,
t: Term) -> Term`; it is ~40 lines with `View`.

---

## 4. Equality and ordering — **[H]**

C++ standard order (`Heap::compare`, `awrterms.cc:576-615`), driven by the `Type` enum:

```
INTEGER < REAL < DATE < ATOM < VAR < STRING < BINARY < FUNC < LIST < TUPLE
```

Rust (`view.rs:349-362`):

```
Var < Int < Date < Real < Atom < Str < Func < Tuple < List < Bin
```

Differences that change observable sort order of mixed data:
1. **Var position**: C++ sorts vars *after* atoms; Rust sorts vars first (Prolog-style).
2. **Binary position**: C++ before compounds; Rust after (the Rust comment claims
   "strings < binaries < compounds" which matches C++/Prolog intent but not the code —
   see idiomatic report **B5**).
3. **Int/Date/Real relative order** differs (`INTEGER<REAL<DATE` vs `Int<Date<Real`).
4. **Numbers of different kinds** are ordered by kind in both systems (C++ `type(t1) <
   type(t2)` short-circuits just like Rust's `kind_order` gate), so parity there — but the
   Rust code comments promise value comparison; pick one and align code+docs.
5. **Same-kind integers**: C++ compares exact ints; Rust converts to `f64` first and loses
   precision ≥ 2^53 (probe-confirmed bug, idiomatic report **B4**).
6. **Compound comparison strategy**:
   * C++ compares FUNC/LIST/TUPLE *element-wise lexicographically* (via `toList`, functor
     first for funcs), shorter-is-prefix → smaller: `[1,2] < [2]`, and `a(1,1) < f(9)`
     because `a < f` regardless of arity.
   * Rust compares **length first**, then functor, then args (`view.rs:276-338`):
     `[2] < [1,2]`, and `f(9) < a(1,1)` because arity 1 < 2.
   * Rust's func rule matches ISO-Prolog standard order (arity, then name, then args) —
     arguably better — but Rust's *list* rule (length-first) matches **neither** C++ nor
     Prolog (Prolog compares lists as nested `'.'/2` cells → lexicographic). Anyone
     sorting lists expects lexicographic. **Recommend**: lexicographic for lists, keep
     arity-first for funcs, and document the deliberate departure from the C++ order.
7. **Equality**: C++ `eq` is structural with intern-based fast paths. Rust `View::eq` is
   structural but compares functors by *handle* (bug, idiomatic report **B3**).

Also missing: arena-level `compare(Term, Term)`/`eq(Term, Term)` conveniences (C++ has
`lt/le/gt/ge` and `HTerm` with `==`/`<`). Rust users must `view()` both sides manually.

---

## 5. Environment and unification (`unify.cc`, `Env`) — **[M]**

Entirely absent in Rust: `Env` (name→term bindings with `bind`/`unbind`/`rebind`/`deref`
with cycle guard/`isBound`) and linear `unify` (no occurs-check). If the Rust crates are
meant to replace the C++ stack for rule/template processing (`rdl.ax`, `tstunify.cc`
use it), this subsystem must be ported. Porting notes:

* C++ `deref` loop-guards by `h.eq(t, s)` against the *original* var only — a 2-cycle
  `X→Y→X` still loops forever… actually it terminates because it re-finds `s`; but a
  3-cycle `X→Y→Z→Y` spins between `Y` and `Z` forever. Port with a proper visited check.
* `unify` has a genuine bug to *not* port: `if(h.length(t2)!=h.length(t2))` compares `t2`
  with itself (`unify.cc:72`) — the arity check is a no-op, so compounds of differing
  length can walk out of bounds. Use `len(t1) != len(t2)`.
* C++ `Env` keys are `h.data(v)` (name bytes) — variables with equal names in different
  scopes alias. Decide whether that is intended before porting.

---

## 6. Printing (`Printer` ↔ `TermDisplay`)

### 6.1 Configurability — **[M]**
C++ `Printer` has `setBinaryDisplayType(BDT_BIN|BDT_HEX)`, `setStringDisplayType(SDT_UTF8|
SDT_PRT)`, `setRealPrecision(n)` (`awrterms.hpp:112-160`). Rust `TermDisplay` has **no
options** (acknowledged as future work in `display.rs:9-16`):

* Binaries always print as `hex{…}` (`display.rs:137-143`); the C++ default `bin{N:raw}`
  form is not producible. Anything downstream that expects `bin{N:…}` (e.g. templates in
  `test.ax`) can't be regenerated.
* No printable-ASCII escape mode for strings (`SDT_PRT` / `toPrintableAsciiString`).
* Reals: C++ prints fixed `%.*f` (default 5 digits); Rust prints shortest-round-trip (and
  `x.0` for integral). Round-trips better **[+]**, but output differs everywhere.
* C++ hex output wraps at 32 bytes/line with `{`/`}` on their own lines for > 64 bytes;
  Rust emits one unbroken line. [L]
* C++ prints top-level lists multi-line (`[\n a,\n b\n]`, `awrterms.cc:1266-1283`);
  Rust single-line. [L]

### 6.2 Atom quoting/escaping — **[M]**
C++ `needQuotes` (`awrterms.cc:1088-1115`) leaves unquoted: lowercase-alnum atoms,
**operator-symbol atoms** (`++`, `<=`, `-`), solo chars, and `[]`/`()`; quoted atoms are
escaped byte-by-byte via `termwtab` printable images (all control chars escaped).
Rust `is_unquoted_atom` (`display.rs:53-60`) allows only `[a-z][A-Za-z0-9_]*`, so every
operator atom prints quoted (`'++'(…)` vs C++ `++(…)`) — cosmetic [L] — but escaping only
handles `'` (`display.rs:67-74`): backslashes and control characters are emitted raw, so
`'a\b'` re-parses as `a<backspace>` — a genuine round-trip breaker (idiomatic report
**B10**). C++ got this right; port the escape table.

### 6.3 String escaping — **[+] with note**
Rust escapes `{`/`}` in strings (`display.rs:83-84`) so interpolation-significant braces
round-trip; legacy C++ did **not** escape braces on output, so C++ `"a{b"` output re-parses
as interpolation — a legacy bug fixed in Rust. Keep, but note it in the divergence docs
(CHANGELOG 0.5.0 mentions it only indirectly via test updates).

### 6.4 Dates — **[M]**
C++ `show` prints `date{MM/DD/YYYY HH:MM:SS}`; Rust prints RFC3339 `date{1970-01-01T00:00:00+00:00}`.
The Rust lexer *can* read the C++ form (`DATE2`+`TIME3`), but the C++ `parseDateExcel`
cannot read the Rust form → **one-way compatibility**. If C++ consumers still exist, add a
legacy date format mode to `TermDisplay`.

### 6.5 `pprint` (TeX) and `Printer::op` — **[✓-ish]**
Declared in `awrterms.hpp:135-139` but **never defined** in the reviewed sources — dead
API on the C++ side. No action needed.

---

## 7. Lexer (`lexer.l` ↔ `term.alex` + `lexer.rs`)

Overall the Rust lexer is a faithful and better-tested port; parity confirmed for: `%` line
comments, nested `/* */`, punctuation & nest counting, `date{N}` epoch form **[+]** (new),
`hex{…}`, `bin{N:…}` byte-counted (CRLF preserved), `bin{label:…label}` heredocs,
`text{N:…}` (CRLF→LF, counted as 1 — matches flex `{NL}`), `text{label:…}`, `{script}` →
string, string/atom escape family (`\xHH`, `\NNN`, `\^X`, `\d \e \a \b \f \n \r \t \v`,
line-splice `\<NL>`, `\.`), string interpolation `"a{X}b"` → `( "a" ++ (X) ++ "b" )`
including the outer paren wrap and `}`-continuation, quoted-functor `'atom'(`, char codes
`0'c` and all `0'\…` escapes, `0x…`/octal/decimal ints, base-N `B'ddd`, EOF-in-mode errors,
`.` at top level as terminator, `'.'` at nesting > 0 as ordinary atom.

Remaining differences:

* **[M]** *Operator classification tokens.* C++ resolves fixity in the lexer via
  `opdefs.opxMap` into 10 token kinds (`op100/op010/op001/op110/fo*`, `at000/fu000`),
  because the C++ `Opx.type` can only hold limited fixity combinations (`optcalc` collapses
  e.g. infix+postfix). Rust defers to two tokens (`AtomOper`/`FuncOper`) + parse-time
  resolution and its `OperDefTab` holds **all four fixities simultaneously** — strictly
  more expressive **[+]** (e.g. `-` infix *and* postfix in `SAMPLE_DEFS`). But the
  `(has_empty, has_non_empty)` conflict check in `lexer.rs:373-408` *errors* on operators
  where one fixity has extra named args and another doesn't ("arguments conflict in op
  defs") — a case C++ could represent (per-fixity `fo*` vs `op*` decision). Corner case;
  verify against real op files.
* **[M]** *Interpolation depends on a defined `++`.* C++ hardcodes op index 0, which the
  `Parser` ctor guarantees (`parser.cc` ctor defines `++`, `-`). Rust looks up `"++"` at
  lex time (`lexer.rs:356,1043`); with an arena lacking default opers this produces
  `op_tab_index: None` and later **panics** in `resolve_ambiguity` (probe-confirmed;
  idiomatic report **B7**). Functional regression vs C++, since Rust's defaults are opt-in.
* **[L]** `0'\^@` accepted in Rust (`[A-Z\@]`), not in C++ (`[A-Z]`). Extension.
* **[+]** Base-N literals: C++ `assert(base>=2&&base<=36)` and `assert(val<base)` —
  crashes on `99'1` / `2'9` in release-with-asserts; Rust bounds the base in the regex and
  `from_str_radix` reports errors.
* **[+]** Overflow: C++ `atoi`/`sscanf` silently wrap 32-bit; Rust errors on i64 overflow.
* **[+]** Octal escapes > 255: C++ truncates via `(unsigned char)`; Rust errors.
* **[+]** Encodings: full WHATWG input transcoding vs C++ byte-passthrough.
* **[L]** C++ `<sH>` hex mode accepts only `{H}{H}` pairs and errors on odd counts via
  fallback; Rust likewise (`HexByte`). Parity.
* **[L]** `0x` with no digits → 0 in both (parity of a shared quirk; consider erroring).

---

## 8. Grammar & parser driver (`term.g`/`parser.cc` ↔ `termx.g`/`parser.rs`)

* **[✓]** Productions map 1:1 (term/eot/empty, func, list, list-with-tail, nil, tuple,
  unit, scalars, infix/prefix/postfix, seq with optional trailing comma). Rust adds
  `Term -> .` (lone dot = empty term) — C++ achieves the same via lexer `eot`+`eos`. Parity.
* **[✓]** Unary tuple unwrap (`(x)` → `x`) and `tuple` display for arity 1: C++
  `LR_PROD_tuple` keeps `vs[base+1]` when 1 element; Rust `ProdID::Tuple` same
  (`parser.rs:427-434`). Note Rust has **no way to construct** a unary tuple from text
  (same as C++); `Term::tuple(a, [x])` from code works. TODO `(expr,)` noted in code.
* **[✓]** Prefix-minus constant folding on int/real literals, only for the bare-atom
  operator form. Parity (`parser.cc:307-327` ↔ `parser.rs:544-568`).
* **[M]** *Ambiguity resolution.* C++ compares `op1.prec` (infix or prefix per conflict id)
  against `op2`'s **infix** slot only (`ind2 = OPX110→OPX010 else type`, `parser.cc:424`).
  Rust compares against the **min/max across op2's infix and postfix** slots
  (`parser.rs:207-286`) and adds explicit error cases when `prec1` falls strictly between
  differing infix/postfix precedences. For operator tables expressible in C++ the outcomes
  match; for the new (Rust-only) infix+postfix combinations behavior is Rust-defined. Fine,
  but document it; and note C++ `ambiguity` *errors* on `assoc1 != assoc2` at equal
  precedence — Rust errors likewise but only when the min==max path is taken; the
  in-between path errors with a different message. Behavior-compatible for legacy tables.
* **[H]** *Named/positional argument arrangement.* C++ `arrangeArgs` (`parser.cc:182-248`)
  processes **all named args first**, then drops positional extras into the **first free
  slot** left-to-right. Rust `normalize_term` (`oper.rs:617-722`) processes args **in
  textual order** and pins a positional extra to **its own positional index**, erroring
  ("cannot redefine argument") if a preceding named arg already claimed that index.
  Example with `op(box(wd,ht),fun,0,none)`: `box(wd=1, 2)` → C++ yields `box(1,2)`…
  actually C++ fills named `wd`=1 then positional `2` → first free slot is `ht` → `box(1,2)`;
  Rust: positional `2` sits at index 1 (`ht`) too — but `box(ht=1, 2)` → C++ `box(2,1)`,
  Rust errors (index 1 taken). Legacy `.ax` files mixing named-then-positional args will
  fail. Decide and document; the C++ fill-first-free-slot rule is what legacy data expects.
* **[H]** *Excess positional args*: C++ raises `parseError("too many arguments …")`;
  Rust **panics** with index-out-of-bounds (probe: `box(1,2,3)` → panic at `oper.rs:677`).
  Details in idiomatic report **B6**.
* **[M]** *`op/…` arity.* C++ `OpDefs::op` consumes `op/4` terms. Rust
  `Arena::define_oper` unpacks **exactly** `op/6` (`oper.rs:415`). Legacy `op/4` *text*
  (e.g. `rdl.ax`, the parser tests' `SAMPLE_DEFS`) still works **only** because the default
  `op` fun-operator definition (with `rename_to=none, embed_type=false` defaults) is
  normalized by the parser into `op/6` — i.e. it works iff (a) the defs go through the
  parser, and (b) the arena has default opers. Programmatic `define_opers(term)` with a
  hand-built `op/4` term fails. Consider accepting arity 4/5 in `define_oper` directly.
* **[M]** *Default operators.* C++ `Parser` ctor **always** defines `++` (infix,500,left)
  and `-` (prefix,800,right); `=` and the `op` fun-def are present but commented out
  (`awrterms.cc:1293-1294`). Rust `define_default_opers` installs `-`, `++`, **and** `=`
  (infix,100,right) **and** `op/…` (`oper.rs:757-806`) — and installs them **only if** the
  user calls `try_with_default_opers`. Net effects:
  1. A Rust arena built with plain `Arena::new()` cannot parse interpolated strings
     (panic) and treats `=`-containing input differently than C++.
  2. A C++ setup that *did* define `=` itself will now collide with Rust's default `=`
     (`define_oper` refuses redefinition — "cannot re-define").
  *Recommendation:* auto-install `++`/`-` in `TermParser::try_new` (matching C++), or make
  the lexer/interpolation path fail soft.
* **[+]** *Rename/embed extensions.* `rename_to`/`embed_fixity` are new capabilities with
  no C++ counterpart. Fine; keep them optional in the surface syntax (see op/4 point).
* **[L]** `scanAll` (debug) and `printMap`/`printStack` debug helpers — Rust uses `log`
  tracing instead. Parity in spirit.
* **[M]** *Error reporting*: C++ reports `stream name + line`; Rust `Span` has line/col
  but several errors lose the stream name (no stream-name concept at all). If multiple
  inputs are parsed, consider carrying an input label in `TermLexer`.

---

## 9. Utilities without Rust counterparts

* `term_utils.h` `TermMaker`: variadic `term(…)`, `list(…)`, `tuple(…)` builders — covered
  by `func!`/`list!`/`tuple!` macros **[✓]**; helpers `reverseList`, `concat`,
  `replaceArg`, `argString/argInt/argReal/argIntTuple/argRealTuple` — small, but they are
  the C++ call-site vocabulary; a `terms-ext` helper module would ease porting. **[L]**
* `dump8` hex dump diagnostics (`awrterms.cc:159-195`) — `{:?}` on `View` covers most needs. **[✓]**
* `Heap::_test` internal dumper — `Arena::stats` + `Debug` cover it. **[✓]**
* `words.cc`, `stream.cc`, Lua bindings (`termslua.cc`), OLE/PDF consumers — out of scope
  for the crates; noted only for inventory completeness.

---

## 10. Already-documented divergences (accepted; no action beyond docs)

* `123e5` accepted as a real (README/CHANGELOG). C++ lexes it as `123` then atom `e5`.
* Dates are Unix-epoch milliseconds `i64` (C++: Excel serial `double`, second resolution in
  `show`, low-mantissa truncation in storage). Rust adds ms precision and many more input
  formats (probe-tested extensively in `lexer.rs` tests). Note §6.4 one-way text compat.
* Handle is 16 bytes vs 8 (design doc `ArenaVsDirect.md`).
* MIT relicense, encodings, spans — additive.

---

## Appendix A — C++-side defects noticed during review (do **not** port)

1. `Env::unify` self-comparison `h.length(t2)!=h.length(t2)` (`unify.cc:72`) — arity check
   is a no-op.
2. `Env::deref` cycle guard only detects cycles that return to the *first* var
   (`awrterms.hpp:717-727`); `X→Y→Z→Y` loops forever.
3. `optcalc` fixity-combination table cannot represent infix+postfix operators
   (`parser.cc:48-54`) — the Rust `OperDefTab` fixes this.
4. Printer does not escape `{`/`}` in strings → interpolation re-parse bug (fixed in Rust).
5. `base'digits` lexer rule relies on `assert` for base/digit validation (`lexer.l:414-437`).
6. 32-bit int overflow wraps silently (`atoi`).
7. `Heap` copy-assignment self-check ok, but `HashTab` copy ctor copies statistics only —
   correctness depends on `Heap` copying `regions` first; fragile coupling.
8. `words.cc` fixed 10 000-byte buffer with no bounds check.

## Appendix B — cross-reference

Findings that are simultaneously "gaps vs C++" and Rust bugs are elaborated with probe
evidence in `fable5-review-arena-idiomatic-rust.md`: B2 (truncate aliasing), B3 (functor
handle equality), B4 (i64-via-f64), B5 (kind-order comment), B6 (normalize_term panic),
B7 (interpolation assert), B10 (atom escaping).
