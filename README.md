# Prolog‑like term library

Copyright (c) 2005–2025 IKH Software, Inc. <support@ikhsoftware.com>
Released under the terms of the GNU Lesser General Public License, version 3.0
or (at your option) any later version (LGPL-3.0-or-later).

This document describes the design and API of the supplied **arena-backed term library**.
The library provides a compact, copyable \[`Term`] type for representing Prolog-like data structures, together with an \[`Arena`] that interns atoms, variables, strings, binaries, and compound terms.
All interned data resides in the `Arena`, while a `Term` itself is just a 16-byte handle containing a tag and an index into the arena’s storage.

Because terms are **immutable**, they can be freely reused and shared across different parts of a program, as well as nested within each other.
Copying or moving a `Term` is cheap: only the handle lives on the stack, while larger payloads are stored once and shared through the arena.

Users interact with the library through three main types:

* **\[`Term`]** – a 16‑byte handle identifying a value.  Values may be integers, floats, dates, atoms, variables, UTF‑8 strings, binary blobs or compound structures (functions, lists, tuples).  This handle implements `Copy`, `Clone`, `PartialEq` and does **not** directly borrow from the arena.
* **\[`Arena`]** – an allocator that interns names and sequence data.  Every `Term` referencing interned data stores the arena’s ID so that an attempt to view a term with the wrong arena fails at runtime.
* **\[`View<'a>`]** – a borrowed representation obtained via `Term::view(&Arena)` or `Arena::view(&Term)`.  A `View` decodes inline data or dereferences indices back into the arena.  It supports pattern‑matching and ordering according to Prolog’s standard term order. Obtaining a view does not allocate: it either returns references to inlined bytes or slices borrowed from the arena.

The crate also provides a trait \[`IntoTerm`] for automatic conversion of many Rust types into `Term` values, and a suite of macros (`list!`, `tuple!`, `func!`, `atom!`, `var!`, `date!`, `unit!`, `nil!`) that make constructing compound terms ergonomic.  The following sections describe each component in detail and illustrate typical usage.

Here is a quick example that demonstrates how to construct terms and inspect them using Rust’s pattern matching:

```rust
use arena_terms::{Arena, func, IntoTerm, list, tuple, var, View};

// create an arena
let mut arena = Arena::new();

// build some primitive terms
let a = arena.atom("hello");
let b = arena.real(3.14);
let c = arena.date(1_640_995_200_000i64);  // 2022-01-01T00:00:00Z

// build a long list from an iterator
let xs = arena.list((0..1_000_000).map(|x| x as f64));

// build a compound term using the func! macro
let term = func![
    "example"; 
    123,                // IntoTerm: integer
    "abc",              // IntoTerm: &str
    list![a, b, c, xs], // nested list (xs is shared)
    tuple!(b, a, xs),   // nested tuple (xs is shared)
    var!("X"),          // variable (implicit arena)
    => &mut arena
];

// inspect the resulting term
if let Ok(View::Func(ar, functor, args)) = term.view(&arena) {
    assert_eq!(functor, "example");
    assert_eq!(args.len(), 5);
    // view nested terms recursively
    match args[2].view(ar).unwrap() {
        View::List(_, elems, _) => assert_eq!(elems.len(), 4),
        _ => unreachable!(),
    }
}
``` 


## Term

A \[`Term`] is an opaque handle that stores a single discriminant and its payload.  On 64‑bit targets the handle occupies exactly 16 bytes; this includes an eight‑bit tag indicating the kind of term and the remaining bytes for the inlined payload or a slice index.  Users never construct `Term` values by directly instantiating the underlying enum – instead they use the provided constructors or macros.

### Primitive constructors

The type provides associated functions to create primitive values:

* **`Term::int(i: impl Into<i64>) -> Term`** – constructs an integer term.  The full two’s‑complement representation is stored.  For example:

```rust
use arena_terms::{Arena, Term};

let t1 = Term::int(42);      // 64‑bit integer
let t2 = Term::int(-7_i32);  // integers are widened to i64
```

* **`Term::real(f: impl Into<f64>) -> Term`** – constructs a 64-bit floating-point (f64) term, storing its complete IEEE 754 double-precision representation.

* **`Term::date(ms: impl Into<i64>) -> Term`** – stores a date as milliseconds since the Unix epoch using a distinct tag.

* **`Term::atom(arena: &mut Arena, name: impl AsRef<str>) -> Term`** – interns an atom name.  Short names (≤14 bytes of UTF‑8) are inlined directly in the handle; longer names are inserted into the arena and the handle stores an index to the interned string.  Atoms are used to represent constant symbols.

* **`Term::var(arena: &mut Arena, name: impl AsRef<str>) -> Term`** – interns a variable name.  Variable names are drawn from a separate namespace but follow the same inlining rules as atoms.

* **`Term::str(arena: &mut Arena, s: impl AsRef<str>) -> Term`** – interns a UTF‑8 string.  Short strings (≤14 bytes) are inlined; longer strings are appended to the arena’s string storage and referenced by index and length.

* **`Term::bin(arena: &mut Arena, bytes: impl AsRef<[u8]>) -> Term`** – interns a binary blob.  Like strings, short slices are inlined while longer slices are appended to the arena’s binary storage.

### Compound constructors

Compound terms are slices of `Term` values stored in the arena. The library provides several constructors:

* **`Term::func(arena: &mut Arena, functor: impl AsRef<str>, args: impl IntoIterator<Item = impl IntoTerm>) -> Term`** – Creates a compound term. If no arguments are supplied, the result is simply an atom. Internally, the functor name is converted to an atom (interned as needed), and both the functor and its arguments are stored consecutively in the arena.

* **`Term::list(arena: &mut Arena, terms: impl IntoIterator<Item = impl IntoTerm>) -> Term`** – Constructs a proper list, represented as a sequence of terms. If the iterator is empty, the atom `nil` (constant `Term::NIL`) is returned.

* **`Term::listc(arena: &mut Arena, terms: impl IntoIterator<Item = impl IntoTerm>, tail: impl IntoTerm) -> Term`** – Constructs an improper list (a list with a tail). If the iterator is empty, the atom `nil` (constant `Term::NIL`) is returned. If the tail is `Term::NIL`, a proper list is constructed; otherwise, the tail is appended to the sequence of list elements.

* **`Term::tuple(arena: &mut Arena, terms: impl IntoIterator<Item = impl IntoTerm>) -> Term`** – Constructs a tuple. Tuples share the same storage mechanism as proper lists. A zero-element tuple yields the atom `unit` (constant `Term::UNIT`).

In addition to these constructors, the type defines two constants:

* **`Term::UNIT`** – The zero-arity tuple, represented by the atom `unit`.
* **`Term::NIL`** – The empty list, represented by the atom `nil`.

### Inspecting terms with `View`

A \[`Term`] can be decoded into a borrowed view using the `view` method.  `Term::view(&self, arena: &Arena) -> Result<View<'_>, TermError>` verifies that the supplied arena matches the term’s arena ID and then decodes inlined data or dereferences indices.  If the wrong arena is passed, an error of type `TermError::ArenaMismatch` is returned.  The [`Arena::view`](#arena) method forwards to `Term::view` and can be used symmetrically.

```rust
use arena_terms::{Arena, Term, View};

let mut arena = Arena::new();
let atom = Term::atom(&mut arena, "hello");
let num  = Term::int(3);
let list = Term::list(&mut arena, [atom, num]);

match list.view(&arena).unwrap() {
    View::List(_, slice) => {
        // slice is &[Term] containing the elements of the list
        assert_eq!(slice.len(), 2);
        assert!(slice[0].view(&arena).unwrap() == View::Atom("hello"));
    }
    _ => unreachable!(),
}
```

Because a `View` borrows from the arena, its lifetime ties together both the arena and the original `Term`.  You must therefore ensure that the arena outlives any view.

## Arena

An \[`Arena`] owns all interned data and ensures that terms remain valid for the arena’s lifetime.  Each arena has a randomly generated `ArenaID`; terms carry this ID so that `view` can detect mismatches.  Creating a new arena is straightforward:

```rust
use arena_terms::Arena;

let mut arena = Arena::new();
```

The arena exposes methods mirroring the constructors on \[`Term`], such as `arena.int`, `arena.real`, `arena.date`, `arena.atom`, `arena.var`, `arena.str`, `arena.bin`, `arena.func`, `arena.list`, `arena.listc` and `arena.tuple`.  Each of these simply calls the corresponding `Term::` constructor but allows you to write code in a fluent style.  The arena also exposes a `stats` method that returns statistics about how many atoms, variables and bytes of string/binary data have been interned.

Interning occurs only when necessary.  Very short names and sequences are stored directly inside the 16‑byte handle; longer data is appended to contiguous storage vectors inside the arena.  The `stats` method allows you to inspect these counts for debugging or tuning purposes.

The following example creates a handful of terms and views them:

```rust
use arena_terms::{Arena, View};

let mut a = Arena::new();
let x = a.atom("foo");
let y = a.var("Bar");
let z = a.list([x, y]);

match a.view(&z).unwrap() {
    View::List(_, slice) => {
        assert_eq!(slice.len(), 2);
        assert!(slice[1].view(&a).unwrap() == View::Var("Bar"));
    }
    _ => unreachable!(),
}

println!("{:#?}", a.stats());
```

`Arena` ensures that terms cannot be misused across arenas.  Storing a `Term` into an arena that it does not belong to (e.g., as an argument to `func`) will not trigger an error, however, dereferencing it via `Arena::view` will return an error.  Therefore, you should treat each arena as an isolated universe of terms.

## View<'a>

The \[`View<'a>`] type is a borrowed enumeration that describes the decoded contents of a term.  It has variants corresponding to each term kind:

```rust
pub enum View<'a> {
    Int(i64),                               // integer values
    Real(f64),                              // floating point values
    Date(i64),                              // date values (milliseconds since Unix epoch)
    Var(&'a str),                           // variable names
    Atom(&'a str),                          // atom names
    Str(&'a str),                           // UTF‑8 strings
    Bin(&'a [u8]),                          // binary slices
    Func(&'a Arena, &'a str, &'a [Term]),   // compound terms (funcs)
    List(&'a Arena, &'a [Term], &'a Term),  // lists
    Tuple(&'a Arena, &'a [Term]),           // tuples
}
```

Obtaining a view does not allocate: it either returns references to inlined bytes or slices borrowed from the arena.  When destructuring a view, you may inspect the functor name and arguments of a compound term or iterate through the elements of a list.  Remember that the `Arena` reference stored in the view must be used when recursively viewing nested terms (the library uses `arena_mismatch` checks to enforce this).

### Ordering and equality

`View` implements `PartialEq`, `Eq`, `PartialOrd`, and `Ord`, following Prolog’s **standard order of terms** with some adaptations.
The ordering is defined first by the *kind* of the term, and then by a *value-based comparison* within that kind:

1. **Variables** — come first, ordered lexicographically by their names.
2. **Integers** — ordered by numeric value.
3. **Dates** — ordered by numeric value (Unix epoch in milliseconds).
4. **Reals** — ordered by numeric value.
5. **Atoms** — ordered lexicographically by name.
6. **Strings** — ordered lexicographically.
7. **Funcs** — ordered first by arity (number of arguments), then by functor name, and finally by lexicographic comparison of their arguments.
8. **Lists** — ordered lexicographically by their elements, with the tail considered last.
10. **Binaries** — ordered lexicographically by their byte values.

This ordering allows you to sort or deduplicate `View` values using standard collections:

```rust
use arena_terms::{Arena, View};
use std::cmp::Ordering;

let mut arena = Arena::new();
let t1 = arena.atom("a");
let t2 = arena.int(42);
let t3 = arena.var("X");

let mut views = vec![t1.view(&arena).unwrap(), t2.view(&arena).unwrap(), t3.view(&arena).unwrap()];
views.sort();

assert_eq!(views[0], View::Var("X"));      // variables come first
assert_eq!(views[1], View::Int(42));       // numbers next
assert_eq!(views[2], View::Atom("a"));     // atoms last here
```

## The `IntoTerm` trait

The crate defines a trait \[`IntoTerm`] used to convert various Rust values into `Term`s when constructing compound values.  Its single method `into_term(self, arena: &mut Arena) -> Term` converts the receiver into a term using the given arena.  Implementations exist for:

* Primitive integers (`i8`, `i16`, `i32`, `i64`, `u8`, `u16`, `u32`) and floats (`f32`, `f64`), which call `Term::int` or `Term::real` respectively.
* Slices of bytes (`&[u8]`), `Vec<u8>`.  These are interned via `Term::bin`.
* `&str`, `Cow<'a, str>` and string types  – interned as UTF‑8 strings via `Term::str`.
* `Term` itself and `&Term` – simply return or copy the handle.
* Closures `FnOnce(&mut Arena) -> Term` – evaluating the closure with the arena allows macros to pass arena reference implicitly.

Because of these implementations you rarely need to call `Term::int` or similar constructors directly when building compound terms.  Instead, you can pass integers, floats, strings and other terms directly into the macros described below and they will automatically be converted.

The following demonstrates `IntoTerm` in action:

```rust
use arena_terms::{Arena, Term};

let list = arena.list([1, 2, 3]);

// Equivalent to:
let list2 = arena.list([Term::int(1), Term::int(2), Term::int(3)]);

assert_eq!(arena.view(&list).unwrap(), arena.view(&list2).unwrap());

// You can also provide closures returning Term.
let lazy = Term::func(&mut arena, "lazy", [|arena: &mut Arena| arena.atom("ok")]);

```

### `AsRef<Term>` implementation

`Term` implements `AsRef<Term>` by returning itself.  This trivial implementation allows a `Term` to be used where an `&Term` is required.  It is most often used internally by macros; you generally do not need to call `as_ref` explicitly.

### `From<T>` implementations for `Term`

Rust’s `From` trait is implemented for common numeric types.  Converting from an integer type (`i8`, `i16`, `i32`, `i64`, `u8`, `u16`, `u32`) into a `Term` calls `Term::int` and widens the value to `i64`.  Converting from a floating type (`f32`, `f64`) calls `Term::real`.  These implementations allow you to write `Term::from(42u8)` or use `.into()` in place of an explicit call to `int` or `real`:

```rust
use arena_terms::Term;

let i: Term = 10u32.into();     // calls Term::int
let f: Term = 3.14f32.into();   // calls Term::real
```

No `From` implementation exists for dates because it would not be clear whether create interger or date term. No `From` implementation exists for vars, atoms, strings, binary blobs because constructing these values always requires an arena.  Use `Term::date`, `Term::atom`, `Term::var`, `Term::str` or `Term::bin` instead.

## Macros: explicit vs. implicit arena

To make term construction more ergonomic the crate exports several macros.  Each macro is defined in two forms:

* **Implicit arena** – the macro call expands to a closure of type `FnOnce(&mut Arena) -> Term`.  You can then pass your arena to this closure.  This allows nested macro calls to share the same arena.  For example, `list![1, 2]` returns a closure that builds a list when given an arena.
* **Explicit arena** – by adding `=> &mut arena` at the end of the macro invocation you can construct the term immediately in a given arena.  The macro simply calls the implicit form and then applies it to the provided arena.

All macros rely on the `IntoTerm` trait to convert their arguments into terms.  Macros for constructing integers, reals, and strings are not provided, since these values can be used directly wherever an `IntoTerm` is expected. In such cases, they are automatically converted into the corresponding integer, real, or string term.

### `list!`

The `list!` macro constructs proper or improper lists.  A zero‑length tuple yields `Term::NIL`. Its syntax is:

```
list![ a, b, c ]  // returns closure: |arena: &mut Arena| arena.list([a.into_term(arena), ...])
list![ a, b, c => &mut arena ]

list![ a, b; tail ]  // improper list with tail
list![ a, b; tail => &mut arena ]
```

Arguments can be any type implementing `IntoTerm`.  The improper form (`; tail`) uses `Term::listc` and stores the tail only when it is not `Term::NIL`.

Example:

```rust
use arena_terms::{Arena, list};

let mut arena = Arena::new();

// Proper list with implicit arena; returns closure
let list_builder = list![1, "two", 3.0];
let my_list = list_builder(&mut arena);

// Improper list with explicit arena
let imp = list![1, 2; 3](&mut arena);

// Equivalent explicit form
let same_list = list![1, "two", 3.0 => &mut arena];
assert_eq!(my_list.view(&arena).unwrap(), same_list.view(&arena).unwrap());
```

### `tuple!`

The `tuple!` macro creates tuples in the same way as lists.  A zero‑length tuple yields `Term::UNIT`.  Syntax:

```
tuple![ a, b, c ]
tuple![ a, b, c => &mut arena ]
```

Example:

```rust
use arena_terms::{Arena, tuple};

let mut arena = Arena::new();

// explicit form
let t = tuple!["hello", 42 => &mut arena);

assert!(t.is_tuple());
```

### `func!`

The `func!` macro constructs compound terms given a functor name and at least one argument.  Zero‑arity functors are represented as atoms, so the macro requires at least one argument.  Syntax:

```
func![ "name"; arg1, arg2, ... ]
func![ "name"; arg1, arg2, ... => &mut arena ]
```

Example:

```rust
use arena_terms::{Arena, func, list, tuple, nil, unit};

let mut a = Arena::new();

let point = func!["point"; 1, 2.0 => &mut a];

// Macros compose: constructing nested terms
let nested = func![
    "nested";
    unit!(),             // 0‑arity tuple
    nil!(),              // empty list
    list![1, 2, 3],      // proper list
    tuple![point, 4],    // tuple containing point
    => &mut a
];

assert!(nested.is_func());
assert_eq!(nested.arity(), 4);
```

### `atom!` and `var!`

The `atom!` macro constructs an atom.  It is mostly a thin wrapper around `Arena::atom` but works with both explicit and implicit arena forms:

```
atom!( "foo" )  // returns closure
atom!( "foo" => &mut arena )
```

Variables can be created with `var!` macro. It is mostly a thin wrapper around `Arena::atom` but works with both explicit and implicit arena forms: 

```rust
let x = var!("X") // returns closure
let x = var!("X" => &mut arena);
```

### `date!`, `unit!` and `nil!`

The remaining macros construct special terms that do not require an arena:

* `date!(ms)` – calls `Term::date(ms)` directly.
* `unit!()` – returns the zero‑arity tuple constant `Term::UNIT`.
* `nil!()` – returns the empty list constant `Term::NIL`.

## Putting it all together

The following example demonstrates how the pieces fit together to build a complex term and inspect it:

```rust
use arena_terms::{Arena, func, IntoTerm, list, tuple, var, View};

// create an arena
let mut arena = Arena::new();

// build some primitive terms
let a = arena.atom("hello");
let b = arena.real(3.14);
let c = arena.date(1_640_995_200_000i64);  // 2022-01-01T00:00:00Z

// build a list and tuple
let lst = list![a, b, c => &mut arena);
let tup = tuple!(b, a)(&mut arena);

// build a compound term using the func! macro
let term = func![
    "example";
    123,               // IntoTerm: integer
    "abc",             // IntoTerm: &str
    lst,               // nested list
    tup,               // nested tuple
    var!("X"),         // variable (implicit arena)
    => &mut arena
];

// inspect the resulting term
if let Ok(View::Func(ar, functor, args)) = term.view(&arena) {
    assert_eq!(functor, "example");
    assert_eq!(args.len(), 5);
    // view nested terms recursively
    match args[2].view(ar).unwrap() {
        View::List(_, elems, _) => assert_eq!(elems.len(), 3),
        _ => unreachable!(),
    }
}
```

This example shows how `IntoTerm` and the macros allow you to mix primitive Rust types, existing `Term`s and closures when constructing compound terms.  Because the macros return closures for implicit arenas, nested calls do not need to mention the arena repeatedly.  When you do provide an explicit arena (via `=> &mut arena`) the closure is applied immediately and returns a `Term`.

