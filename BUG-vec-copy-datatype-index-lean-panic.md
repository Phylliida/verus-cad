# Bug: `--lean-backend` panics on exec indexing of a `Vec<T>` whose element `T` is a user-defined `#[derive(Copy)]` datatype

## Summary

Under `--lean-backend`, **indexing a `Vec<T>` in exec code where `T` is a user-defined
`Copy` datatype** (struct or enum) panics the Lean backend during expression lowering:

```
thread '<unnamed>' panicked at lean_verify/src/expr_shared.rs:831:5:
tuple_field_accessor: arity 1 < 2 — 0-tuple (unit) and 1-tuple shouldn't reach
field accessor synthesis. n=0. If this fires, please open an issue (probable
Verus rebase shape drift).
```

The panic is the deliberate `assert!(arity >= 2)` guard inside `tuple_field_accessor`
(it is being called with `arity == 0`). The panic is **fatal** — it aborts the entire
crate verification (a destructor then re-panics with `dropped, expected call to
into_inner`), so a single offending function takes down `./check.sh` for the whole crate.

`Vec<primitive>` (e.g. `Vec<u64>`, `Vec<usize>`) is **unaffected**. Non-`Copy` datatype
elements (which must be accessed by borrow) are **unaffected**. The trigger is specifically
a `Copy` *user datatype* element.

## Environment

- tactus commit `81f9fe3` (`lean_verify: productionize autoImplicit guardrail`, 2026-06-08)
- Verus version `0.2026.06.08.9439365.dirty`
- Invocation: `verus --lean-backend [--crate-type=lib] FILE.rs`

## Minimal reproducer

```rust
use vstd::prelude::*;
verus! {
#[derive(Clone, Copy)]
pub struct Foo { pub a: usize }

pub fn f(w: &Vec<Foo>) -> usize
    requires w@.len() > 0,
{
    let r = w[0];   // <-- indexing Vec<Foo> (Foo is Copy) panics the Lean backend
    r.a
}
fn main() {}
}
```

`verus --lean-backend repro.rs` → panic (above). An identical file with
`pub fn f(w: &Vec<usize>) ...; let r = w[0]; r` verifies (`2 verified, 0 errors`).

(A runnable copy is saved alongside this file: `BUG-vec-copy-datatype-index-lean-panic.repro.rs`.)

## Expected behavior

Verify (or, if genuinely unsupported, a graceful "unsupported" diagnostic rather than a
panic — cf. the clean `tactus_auto rejected this fn: IntegerTypeBound(...)` errors).

## Reproducer matrix (the boundary)

All snippets are `fn f(w: &Vec<T>) -> ... requires w@.len() > 0`. `Foo` = a one-field
struct; `Sym` = a two-variant enum `{ Gen(usize), Inv(usize) }`.

| # | element `T` | `Copy`? | body | result |
|---|---|---|---|---|
| G2 | `u64` | (builtin) | `g(&w[0])` | ✅ verifies |
| K2 | `usize` | (builtin) | `let r = w[0]; r` | ✅ verifies |
| K3 | `Foo` | **no** | `let r: &Foo = &w[0]; r.a` | ✅ verifies (borrow of non-Copy) |
| L1 | `Foo` | **yes** | `let r = w[0]; r.a` | 💥 panic |
| L2 | `Foo` | **yes** | `let r: &Foo = &w[0]; r.a` | 💥 panic |
| L3 | `Foo` | **yes** | `let r = &w[0]; r.a` | 💥 panic |
| G1 | `Sym` | yes | `g(&w[0])` | 💥 panic |
| W1 | `Sym` | yes | `g(w[0])` (by value) | 💥 panic |
| J1 | `Sym` | yes | `let r = &w[0];` (unused, no call) | 💥 panic |

Conclusions:
- **`Copy` on a *user* datatype element is the trigger.** K3 vs L2 is the controlled
  pair: identical source, only `#[derive(Clone, Copy)]` differs → verify vs panic.
- It is **not** the `&`, **not** the function call, **not** the by-value move — every
  form of *using* a `Vec<CopyDatatype>` index panics (L1/L2/L3, G1/W1/J1).
- Builtin `Copy` types (`u64`/`usize`) are fine (G2/K2), so it's about how a *user
  datatype*'s `Vec`-index value is lowered, not `Copy`-ness per se.
- Passing an already-`&T` value straight through (no `Vec` index) is fine — e.g.
  `fn(x: &Foo) { g(x) }` and `fn(x: Foo) { g(&x) }` both verify. The `Vec` index is essential.

## Root-cause locus

`lean_verify/src/expr_shared.rs:831`, `tuple_field_accessor(arity, n)` — guarded by
`assert!(arity >= 2)` with the comment *"Verus shouldn't produce 0- or 1-tuples here
(unit type lowers to no field access)"*. The `Vec`-index lowering path for a `Copy`
user datatype is reaching this with `arity = 0, n = 0`. Likely the datatype's
clone/copy-out-of-index lowering synthesizes a (spurious) tuple-field projection on
something that lowers to the unit/0-tuple shape — consistent with the "probable Verus
rebase shape drift" note. A `Vec`-of-primitive index does not take this path.

## Impact

- Blocks porting `verus-group-theory/src/runtime.rs` (the exec/runtime layer:
  `RuntimeSymbol` is a `#[derive(Copy)]` enum stored in `Vec<RuntimeSymbol>` and indexed
  throughout, e.g. `is_inverse_pair_exec(&w[i], &w[i+1])` in `find_cancellation_exec`).
- Because the panic is fatal, it aborts whole-crate `./check.sh`, masking everything else.
  (Per-module `--verify-module M` is a usable interim workaround for the *other* modules.)
- **Everything else verifies verbatim.** All the ghost/spec/proof mathematics ported from
  `verus-group-theory` (including the full general Britton's lemma `britton_via_tower`,
  194 verified, and the 12.4k-line `normal_form_afp_textbook`, 231 verified) goes through
  the Lean backend with zero changes. This bug is confined to the exec layer.

## Workarounds

- **None clean for `Copy`-datatype `Vec` elements.** Every index form panics (L1/L2/L3).
- Making the element **non-`Copy`** and accessing via explicit borrow (`let r: &T = &w[i]`)
  avoids it (K3) — but that requires restructuring exec algorithms that rely on `Copy`
  (push-by-value, etc.), so it is not a drop-in fix for `runtime.rs`.
- Since the affected code is purely the exec layer (off the Britton/Higman *math* path),
  the port can proceed on the ghost mathematics and defer the exec layer until this is fixed.

## Secondary, already-known limitation encountered (not this bug)

`todd_coxeter.rs` exec functions using `usize::MAX` produce 9 clean (non-panic) errors:
`tactus_auto rejected this fn: IntegerTypeBound(UnsignedMax): non-constant bit width is
not supported` (`ArchWordBits`). The error itself points to tactus `DESIGN.md` "Known
deferrals", so this is an already-documented deferral, noted here only because it surfaced
in the same port. Minimal repro: `fn f(w: &Vec<u64>) -> usize requires w@.len() < usize::MAX { 0 }`.
