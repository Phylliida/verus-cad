# Closed-evaluation discipline (learned 2026-07-28, phys-05a / scene M1)

The problem: a scene proves `computed == expected` for a CLOSED rational
value (unit square area, centroid, inertia). Everything is concrete — yet
asserts like `vcross2(a[0], a[1]) == from_int_spec(0)` fail.

## What Z3 does NOT do

1. **It does not chain nested open-spec-fn unfolds into a struct
   equality.** `mul_spec`/`sub_spec`/`add_spec` are open and unfold ~1
   level per trigger, but a 5-deep chain (`vcross2 → mul ×2 → sub → add
   → neg`) will not reduce to `Rational { num: v, den: 0 } == from_int(v)`
   on its own. You must stage `.num` and `.den` separately, then conclude
   struct equality (the `lemma_orient_closed` pattern from S3).
2. **It does not multiply two compound closed int terms without nlsat.**
   `assert((1*1 - 0*1) * (1*1 + 0*0 + 1*1 + 0*1 + 1*1 + 1*1) == 4)` FAILS
   plain — the product of two non-literal terms is nonlinear to Z3 even
   though both sides are constants. `by (nonlinear_arith)` discharges it
   instantly. (Zero annihilation IS a rewrite rule, so `0·x == 0` works
   without the pin — which is why only *some* closed identities fail.)
3. **Per-function error caps hide the root cause.** Verus reports ~2-3
   errors per function; the reported assert may be downstream of the real
   failure. For full output, bypass check.sh and run cargo-verus directly:

   ```sh
   cd verus-physics2d
   export PATH="$PWD/../verus-dev/source/target-verus/release:$PATH" \
          VERUS_Z3_PATH=$PWD/../verus-dev/source/z3 \
          RUSTUP_TOOLCHAIN=1.94.0-x86_64-unknown-linux-gnu
   cargo-verus verify --manifest-path Cargo.toml -p verus-physics2d -- \
     --verify-module scenes -V cache --triggers-mode silent --multiple-errors 20
   ```

## What works (the M1 pattern)

- **Structural `*_closed_int` micro-lemmas** (scenes.rs, near the M1
  lemmas): `lemma_raw_mul_closed_int/add_closed_int/sub_closed_int` prove
  `from_int(a) ⊕ from_int(b) == from_int(a⊕b)` as STRUCTURAL equalities
  (all from_int values have `den == 0`, so the den formula collapses).
  Structural `==` then propagates by plain substitution — no eqv
  congruence chaining needed. Packaged variants: `lemma_m1_vcross_closed`,
  `lemma_m1_vadd_closed`, `lemma_m1_vdot_closed`, `lemma_m1_vscale_closed`,
  `lemma_m1_inertia_term_closed`, and `lemma_raw_mul_frac_int` /
  `lemma_raw_mul_int_frac` for `from_frac(1,d) · from_int(m) ==
  from_frac(m,d)` (both need `requires d > 0` — from_frac_spec's
  recommends, and the den-field formula `(d−1)·0 + (d−1) + 0`).
- **A tiny spec ctor for points** (`iv2(x, y)`) — struct literals in
  asserts are a parsing/matching hazard (workspace pitfall list); the
  ctor also gives a single name for congruence to rewrite through.
- **One proof fn per closed quantity** (`lemma_m1_area2`,
  `lemma_m1_centroid`, `lemma_m1_inertia`) with ensures carrying ONLY
  that quantity's closed value. Do NOT put ~100 closed asserts in one
  proof block — the simplifier chokes (R5) and error caps make diagnosis
  miserable. The scene just calls the three lemmas and wires exec
  results to them.
- **Chain unfolds are fine plain**: recursion-step asserts like
  `chain_cross_sum(a, 2) == chain_cross_sum(a, 1).add_spec(cross)` go
  through without help; it's the *leaf arithmetic* that needs the helpers.
- **eqv finals need denom staging too**:
  `from_frac(3,6).eqv_spec(from_frac(1,2))` fails until you assert
  num/denom of both sides and restate the eqv as its cross-multiplied
  form `(3 * 2 == 1 * 6)`.

## Workflow notes

- `check.sh` full-crate runs are ~1–8 min warm; the MCP `verus_check`
  10-min cap is too short for the scenes module — run check.sh in the
  background or use the direct cargo-verus invocation above (module-only
  runs of scenes are ~1–2 min).
- Scenes register as plain `pub fn scene_*() -> (out: bool)` with
  `ensures out == true` — no test harness; the proof IS the test.
