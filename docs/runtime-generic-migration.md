# Runtime Generic Migration Guide

## Overview

The runtime layer across verus-cad is being migrated from hardcoded `RuntimeRational`/`Rational` to generic `R: RuntimeOrderedFieldOps<V>, V: OrderedField`. This allows runtime geometry, linear algebra, and GUI code to work over any exact arithmetic type (rationals, quadratic extensions, fixed-point, etc.).

## Current State

### Completed
- **verus-algebra** (351 verified): `RuntimeRingOps`, `RuntimeFieldOps`, `RuntimeOrderedFieldOps` traits with `View<V=V>` supertrait. `min`/`max`/`clamp` as default methods. All ensures use `@` (View).
- **verus-rational** (726 verified): `RuntimeRational` impl of all three trait levels.
- **verus-linalg** (645 verified): All 8 runtime files generic (`RuntimeVec2<R,V>`, `RuntimeVec3<R,V>`, `RuntimeVec4<R,V>`, `RuntimeMat2x2<R,V>`, `RuntimeMat3x3<R,V>`, `RuntimeMat4x4<R,V>`, `RuntimeQuat<R,V>`). Clean method names (`add`, `sub`, `dot`, `cross`, etc.).
- **verus-geometry** (606 verified): All runtime files generic. `RuntimePoint2<R,V>` → `Point2<V>`, `RuntimePoint3<R,V>` → `Point3<V>`. Correct type separation: `Point.sub(Point) → Vec`, `Point.add(Vec) → Point`.
- **verus-topology** (220 verified): All 3 runtime files generic.
- **verus-gui** (1157 verified): Core types generic + 7 layout/utility files converted.

### Remaining (verus-gui)
- 23 of 34 runtime files still concrete
- Bottleneck: `widget.rs` (2739 lines) — all other widget_*.rs and layout files depend on it
- Text model files (4 files, ~4700 lines) should stay concrete (they're about Unicode, not field arithmetic)

## Key Architecture Decisions

### 1. `RuntimeRingOps` requires `View<V=V>`

The trait hierarchy is:
```
RuntimeRingOps<V: Ring>: Sized + View<V = V>
RuntimeFieldOps<V: Field>: RuntimeRingOps<V>
RuntimeOrderedFieldOps<V: OrderedField>: RuntimeFieldOps<V>
```

The `View<V=V>` supertrait means any `R: RuntimeRingOps<V>` supports the `@` operator, and `r@` gives the spec-level `V` value. This is critical — it means generic ensures can use `self@`, `out@`, `rhs@` just like concrete code, eliminating the `@` vs `.model@` bridging problem.

**Implication for new types**: Any type implementing `RuntimeRingOps<V>` must also implement `View` with `type V = V`. For `RuntimeRational`, this is already satisfied. For `RuntimeQExt`, a View impl needs to be added.

### 2. Generic View impls on runtime structs

Runtime structs like `RuntimeSize<R, V>`, `RuntimeNode<R, V>` implement `View` generically:
```rust
impl<R: RuntimeOrderedFieldOps<V>, V: OrderedField> View for RuntimeSize<R, V> {
    type V = Size<V>;
    open spec fn view(&self) -> Size<V> { self.model@ }
}
```

This means `size@` works in both generic and concrete code, producing `Size<V>`. The ensures of generic functions can use `@` naturally.

### 3. Type aliases for backwards compatibility

During migration, `mod.rs` provides type aliases:
```rust
pub type RuntimeSize = size::RuntimeSize<RuntimeRational, Rational>;
pub type RuntimeLimits = limits::RuntimeLimits<RuntimeRational, Rational>;
pub type RuntimePadding = padding::RuntimePadding<RuntimeRational, Rational>;
pub type RuntimeNode = node::RuntimeNode<RuntimeRational, Rational>;
```

Unconverted files import from `crate::runtime::RuntimeSize` (the alias). Converted files import from `crate::runtime::size::RuntimeSize` (the generic type).

### 4. Concrete-only methods on the concrete instantiation

Methods that use Rational-specific APIs (`normalize()`, `from_int()`, `normalized_spec()`, `eqv_spec()`) live in a separate impl block on the concrete type:
```rust
impl RuntimeSize<RuntimeRational, Rational> {
    pub fn zero_exec() -> (out: Self) { ... }  // uses RuntimeRational::from_int(0)
    pub fn normalize_exec(self) -> (out: Self) { ... }  // uses .normalize()
}
```

Generic code uses `x.zero_like()` and `x.one_like()` from the trait instead.

## Conversion Pattern

For each file, the mechanical changes are:

### Imports
```rust
// Old
use verus_rational::RuntimeRational;
use crate::runtime::{RationalModel, copy_rational};
use crate::runtime::RuntimeSize;

// New
use crate::runtime::size::RuntimeSize;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::traits::runtime::*;
```

### Function signatures
```rust
// Old
pub fn layout_exec(limits: &RuntimeLimits, spacing: &RuntimeRational) -> (out: RuntimeNode)

// New
pub fn layout_exec<R: RuntimeOrderedFieldOps<V>, V: OrderedField>(
    limits: &RuntimeLimits<R, V>, spacing: &R,
) -> (out: RuntimeNode<R, V>)
```

### Spec references
```rust
// Old (uses View @, works only for concrete types)
out@ == linear_layout::<RationalModel>(limits@, padding@, spacing@, ...)

// New (uses View @ via generic View impl — works for ANY R, V)
out@ == linear_layout::<V>(limits@, padding@, spacing@, ...)
```

### Scalar operations
```rust
// Old
RuntimeRational::from_int(0)        →  spacing.zero_like()
RuntimeRational::from_int(1)        →  spacing.one_like()
copy_rational(&x)                   →  x.copy()
a.min(&b) / a.max(&b)              →  a.min(&b) / a.max(&b)  (same! now on trait)
```

### Child sizes in ensures
```rust
// Old
Seq::new(child_sizes@.len() as nat, |i: int| child_sizes@[i]@)

// New (identical! @ works via generic View on RuntimeSize)
Seq::new(child_sizes@.len() as nat, |i: int| child_sizes@[i]@)
```

Note: for `RuntimeSize<R,V>`, `child_sizes@[i]@` goes through `View::view()` which returns `self.model@`. For `Vec<RuntimeSize<R,V>>`, `child_sizes@` goes through Vec's View giving `Seq<RuntimeSize<R,V>>`. Then `[i]@` calls View on the element.

## Known Issues

### 1. Z3 View unfolding triggers

Sometimes Z3 can't see through the generic View impl. The fix is an explicit trigger:
```rust
assert(x@ === x.model@);  // === forces syntactic unfolding
```

This was needed in `widget_grid.rs` where `child_nodes@[j]@` needed Z3 to unfold View.

### 2. `child_sizes@[i]@` bridge for Seq::new closures

When a generic function's ensures builds a spec sequence with `Seq::new(... |i| child_sizes@[i]@)`, and a caller's proof also builds the same sequence, Z3 may treat the two Seq::new closures as different terms. The bridge pattern:
```rust
assert forall|j: int| 0 <= j < child_sizes@.len() implies
    child_sizes@[j]@ == (#[trigger] child_sizes@[j]).model@
by {};
assert(child_sizes_seq =~= Seq::new(... |i| child_sizes@[i].model@));
```

This connects the caller's `@`-based sequence to the generic function's `@`-based sequence (which internally unfolds to `.model@`). With the View supertrait on RuntimeRingOps, this should be less needed.

### 3. `RuntimeRational::from_int(2)` for division

`align_offset_exec` divides by 2 for centering. In generic code:
```rust
let two = available.one_like().add(&available.one_like());
proof {
    // 0 < 1+1, so 1+1 ≢ 0 (required for div precondition)
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_zero_lt_one::<V>();
    V::axiom_lt_iff_le_and_not_eqv(V::zero(), V::one());
    verus_algebra::lemmas::ordered_ring_lemmas::lemma_add_pos_nonneg::<V>(V::one(), V::one());
    V::axiom_lt_iff_le_and_not_eqv(V::zero(), V::one().add(V::one()));
    V::axiom_eqv_symmetric(V::zero(), V::one().add(V::one()));
}
diff.div(&two)
```

### 4. verus-quadratic-extension needs View impls

`RuntimeQExt<FV, R, F>` needs to implement `View` to satisfy the `RuntimeRingOps` supertrait. Also needs `.model()` replaced with `@` throughout. And all callers that use `.model()` on generic `F` params need to use `@` instead.

## Migration Order for verus-gui

The dependency graph determines the order:

### Phase 1: Already done ✓
- Core types: `size.rs`, `limits.rs`, `padding.rs`, `node.rs`
- Layout algorithms: `linear.rs`, `stack.rs`, `wrap.rs`
- Utilities: `diff.rs`, `hit_test.rs`, `animation.rs`, `interaction.rs`

### Phase 2: widget.rs (the bottleneck)
- 2739 lines, recursive enum types, master layout dispatch
- All enum types need `<R, V>`: `RuntimeWidget<R,V>`, `RuntimeLeafWidget<R,V>`, etc.
- `layout_widget_exec`, `merge_layout_exec`, `normalize_widget_exec` all need conversion
- Every `RationalModel` → `V`, every `RuntimeRational` → `R`
- ~500 `@` references — most should work via generic View, some may need triggers

### Phase 3: Widget callers (after widget.rs)
- `widget_sized_box.rs` (92 lines)
- `widget_margin.rs` (118 lines)
- `widget_aspect_ratio.rs` (133 lines)
- `widget_scroll.rs` (113 lines)
- `widget_grid.rs` (410 lines)
- `widget_absolute.rs` (199 lines)

### Phase 4: Layout algorithms with scalar Vecs
- `absolute.rs` (156 lines) — has `Vec<R>` offset params
- `flex.rs` (503 lines) — has `Vec<R>` weight params
- `grid.rs` (400 lines)
- `listview.rs` (609 lines)

### Phase 5: Remaining utilities
- `scroll.rs` (177 lines) — has Rational-specific `add_spec`/`lt_spec` in spec fn
- `draw.rs` (352 lines)
- `event.rs` (320 lines), `event_helpers.rs` (325 lines), `event_routing.rs` (298 lines)
- `measure.rs` (402 lines), `measure_helpers.rs` (328 lines)
- `cache.rs` (549 lines)

### Phase 6: Keep concrete
- `text_model.rs` (3178 lines) — Unicode/string operations
- `session_helpers.rs` (909 lines) — text editing session
- `session.rs` (335 lines) — text editing session
- `text_input.rs` (240 lines) — text input config

## Helper Functions Available

From `verus_algebra::traits::runtime`:
- `r.add(&s)`, `r.sub(&s)`, `r.mul(&s)`, `r.neg()`, `r.div(&s)`, `r.recip()`
- `r.eq(&s)`, `r.le(&s)`, `r.lt(&s)`
- `r.copy()`, `r.zero_like()`, `r.one_like()`
- `r.min(&s)`, `r.max(&s)`, `r.clamp(&lo, &hi)` (default methods on trait)
- `r@` — spec-level value (via View supertrait)
- `r.wf_spec()` — well-formedness predicate

For structs: `RuntimeSize::new(w, h)`, `.copy_size()`, `.from_axes_exec(axis, main, cross)`, `.main_exec(axis)`, `.cross_exec(axis)`, `.eq_exec(&rhs)`

Concrete-only: `RuntimeSize::zero_exec()`, `.normalize_exec()`

## Verification Tips

1. **When converting a file**: change ensures from `out@ == spec_fn::<RationalModel>(limits@, ...)` to `out@ == spec_fn::<V>(limits@, ...)`. Since `@` works via generic View, most ensures clauses need only the type parameter change.

2. **If Z3 can't chain through View**: add `assert(x@ === x.model@)` with `===` (syntactic equality) to force unfolding.

3. **For Seq::new closure mismatches**: assert extensional equality `seq1 =~= seq2` when two Seq::new expressions with different closures should produce the same sequence.

4. **For `from_int(0)` replacement**: use any available `R` reference: `spacing.zero_like()`, `limits.min.width.zero_like()`, etc.

5. **For `from_int(2)` (division by 2)**: construct via `one_like().add(&one_like())` and prove `!two.eqv(zero)` via ordered field positivity lemmas.
