# Exec feasibility: rational witness blowup and the normalize remedy

Date: 2026-07-31 (phys-06 pre-flight, SPEC-phys06 §3 item 2)

## What we measured

First compiled run of the engine (cargo-verus build --release, bench bins
`src/bin/s1_bench.rs`, `s1_scaling.rs`, `rational_blowup.rs` — unverified
harnesses, plain `fn main` + `Instant`).

`scene_s1` (1000 zero-gravity free-flight steps) did **not finish in 300 s**.
Per-step cost (2 bodies, ω = 0, values mathematically constant):

| step | ms | | step | ms |
|---|---|---|---|---|
| 0 | 0.5 | | 6 | 65.6 |
| 2 | 1.2 | | 8 | 873 |
| 4 | 6.9 | | 10 | 12,280 |
| 5 | 20.0 | | 12 | 189,099 |

~4× per step, cleanly exponential. Step 20 would take days.

## Root cause

Witness limb counts double every step in `rot.c`/`rot.s` (19 → 57 → 132 →
282 → 581 → 1181 → … limbs), while `vel`/`pos`/`omega` stay tiny.

Exec `RuntimeRational` add/sub multiply denominators with no reduction.
The RotQ compose `c' = c·c_t − s·s_t` subtracts two products, so the result
denominator is the product of BOTH product denominators:
`L(k+1) ≈ 2·L(k) + const`. Even with t ≡ 0 the unreduced t² terms carry
~20-limb denominators, so the squaring never collapses. Any add-of-products
in a value's update chain does this; the rotation compose is just the first
one hit. This would blow up ANY multi-step run, contacts or not.

## Remedy (validated)

`RuntimeRational::normalize()` (runtime_rational.rs:1329) already exists and
is fully proven: `out@.eqv_spec(self@) && out@.normalized_spec()` via exec
Euclidean `gcd_bignat` + `div_rem`. It is stronger than D10's
untrusted-reducer design (propose + one cross-multiply check) — no new
proof work needed for canonicalize. 06c scope shrinks accordingly.

Normalizing all body fields + `angle_err` after each step: rot.c collapses
to (1,1), normalize costs ~0.05 ms/step, step cost drops from exponential
to ~0.5 ms + 0.17 ms·k creep (see caveat). Projection: full S5 (2000
steps, PGS + certificate) is feasible — minutes, not days.

**Consequence for the plan: denominator hygiene moves from 06c to 06a.**
Canonicalize at step boundaries (and between PGS iterations if needed) is
a hard requirement for ANY scene to run compiled, not an optimization.
D10 sanctions this: value-preserving, no ledger entry, eqv-seams at
explicit call sites.

## Caveat: normalize's zero case doesn't reduce

`angle_err` (value exactly 0 in ω=0 scenes) kept growing +51 limbs/step
*despite* normalize: the zero-numerator branch of `normalize` keeps the
original witnesses ("current form is valid; skip GCD") and only swaps the
ghost model to canonical zero. A zero with a 1000-limb denominator stays
1000 limbs. This is the source of the residual +0.17 ms/step creep, and it
matters exactly for S5-style scenes (stacked boxes have ω = 0).

Fix: make the zero branch return `from_int(0)` witnesses (0/1). The same
ensures still hold (wf: 0·1 == 0·1; eqv via lemma_eqv_zero_iff_num_zero;
normalized via lemma_from_int_is_normalized). Small verus-rational patch,
do it in the phys-06 pre-work commit.

## Bench infrastructure (keep)

- Bins live in `src/bin/` (autobins, no Cargo.toml change), plain Rust,
  no `verus!` wrapper, call pub exec fns directly.
- Build: MCP `verus_compile` (cargo-verus build --release). First build
  verifies the whole lib (~10+ min, two MCP client timeouts — the server
  keeps going, retry and it's cached); adding a new bin afterwards
  rebuilds in seconds.
- Lib modules stay `#[cfg(verus_keep_ghost)]`-gated; bins compiled by
  cargo-verus see everything, no lib.rs changes needed.
- Witness size probe: `r.numerator.magnitude.limbs_le.len()` /
  `r.denominator.limbs_le.len()` (all fields pub).
