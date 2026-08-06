# PLAN: full Lean verification of the color census (2026-07-31)

**Goal.** A kernel-checked theorem, in the spirit of
`no_aperiodic_wang_cube_anyK` (bump/dent track):

> **No equal-color Wang cube — any grid K, any palette ≥ 2 — is an
> aperiodic einstein.** Every equal-color decoration that tiles ℤ³ admits
> a fully periodic tiling.

The computational half is finished: all 414,079 canonical color profiles
are classified (last-wins over `classify_color.jsonl`): **41,824
periodic**, **372,254 box-empty**, and canon 755 (killed by the density
lemma). This document is the roadmap for making that classification
*machine-checked in Lean*, with the smallest possible trust base.

## Trust base conventions

- Kernel + `native_decide` (`Lean.ofReduceBool`, `Lean.trustCompiler`) —
  the standard this project already uses for table/census checks.
- No new axioms. The one existing trust-debt analogue
  (`frontierEmptyFacts` in the bump/dent track, externally cake_lpr-checked)
  is listed under R6: the same infrastructure that discharges R2 here can
  retire it there.

## State of play (done)

| piece | where | status |
|---|---|---|
| density lemma (sharp: `(|A|−|B|)·L ≤ 6`) | `ColorDensity.lean` | proven |
| canon 755 empty by counting | `AnyK3DColorDensity.lean` | proven |
| **176,197** empty profiles, batch-verified | `AnyK3DDensityCheck.lean` + 12 chunks | proven |
| torus checker + soundness | `AnyK3DColorPeriodic.lean` | proven |
| **41,824** periodic profiles, batch-verified | `AnyK3DColorPeriodicAll.lean` + 5 chunks | proven |
| **196,058** empty profiles, cake-backed axiom + inheritance | `AnyK3DColorEmpty.lean` (+`Check`/`Data`) | proven (R2) |
| **R3** census completeness | `AnyK3DColorComplete.lean` + coverage chain | **proven (2026-08-04)** |
| **R4** assembly | `AnyK3DColorMain.lean` | **proven (2026-08-04)** |

**THE COLOR THEOREM IS PROVEN** (`AnyK3DColorMain.lean`):

> `no_aperiodic_equal_color_wang_cube (T K : ℕ) (d : CDec T K)
>   (h : CTiles T K d) : CPeriodicallyTiles T K d`

Axiom footprint (`#print axioms`): `propext`, `Classical.choice`,
`Quot.sound`, `Lean.ofReduceBool`/`Lean.trustCompiler`
(`native_decide`), `colorFrontierUnsat` (the declared cake_lpr
trust debt — same profile as bump/dent's `frontierEmptyFacts`; the
bump/dent axiom is NOT in the color theorem's footprint).

## Remaining work

### R1. Periodic tier batch ✅ DONE (2026-08-02)

- 41,824 torus witnesses regenerated (checkpointed re-solve, 0 failures,
  avg 34 cells/torus), rectangularized to plain tori, packed into 5
  chunks; batch `native_decide` + `torusOK_sound` discharge each
  profile's `PeriodicRelTiles`. `periodic_total : ... = 41824`
  (`AnyK3DColorPeriodicAll.lean`, lean-flocq `fb613ef`).

After R1: **218,021 / 414,079 = 52.6%** of the census kernel-verified.

### R2. Empty remainder: 196,058 box-UNSAT profiles

Breakdown: 195,813 at 3³, 241 at 5³, 4 at 6³. (The 3 empty7 verdicts and
755 are already density-covered.)

**Decision (2026-08-03, probe): the cake_lpr route.** Measured on a
typical color 3³ profile (648 vars, 34,911 clauses): CaDiCaL refutes in
47 ms (214 KB text LRAT); cake_lpr verifies the same cert in **0.093 s**;
in-Lean `verifyCert` stack-overflows at default stack and runs >17 min
even with a 4 GB thread stack (consistent with the M5 probe: >10 min for
one 43 KB cert). In-Lean per-cert checking is ~4 orders of magnitude too
slow for 196k profiles; the solver stays untrusted, the CakeML-verified
checker re-checks every cert, and the Lean side takes an axiom matching
`frontierEmptyFacts`' trust profile.

**Frontier compression (done).** The 196,058 empties reduce to **65,250
locally-maximal empty masks**; every empty profile has a frontier
superset, and emptiness transports downward by `tiling_mono` (already
proven). Certs only for the frontier; the 130,808 subset profiles inherit
via a `maskLe` batch check (`native_decide`, trivial per pair).

**Pipeline (running).** `gen_color_empty_certs.py`: Lean `ExportEmptyCNF`
(the same encoder whose `empty_sound` is proven) → cadical `--lrat` →
cake_lpr verify (checkpointed, certs deleted after). ~1.7 s/CNF export,
~0.15 s solve+verify per mask — hours of wall time, not days.

**Lean side (done 2026-08-03).** `AnyK3DColorEmpty.lean` (lean-flocq
`716656f`): one TRUST DEBT axiom `colorFrontierUnsat` over the 65,250
frontier jobs (external evidence: `color_frontier_verified.txt`),
discharged to `¬∃ IsTiling` via the already-proven `empty_sound`; plus
`colorEmpty_of_inheritance` closing the 130,808 subset profiles via a
batch-`native_decide`'d `maskLe` + `tiling_mono`. **All 196,058 box-UNSAT
profiles are now covered**, at exactly the bump/dent track's trust
profile. (Implementation note: the data is accessed through an
`@[irreducible]` index accessor — appended-array literals in unification
position caused unbounded whnf blowups; batches and native_decide are
unaffected.)

### R3. Census completeness ✅ DONE (2026-08-04)

**`color_census_complete (T K : ℕ) (d : CDec T K) :
profileMask (cheldOf T K d) ∈ censusFastC.toList`** — every equal-color
decoration's profile is enumerated by the Lean-native color census, for
ANY grid K and ANY palette T (no `1 ≤ K` side condition — see below).
Modules:

- `AnyK3DColor.lean` — `CDec T K`, `ceqHolds` (patterns identical
  through the twist), `ccompat`, `cheldOf`, `ccompat_factors`
  (K-vanishing; same `tables_norm` + twisted symmetry as M1).
- `AnyK3DColorGain.lean` — the 8-element gain group (grid isometries
  only, signs +1): `cact`/`cmul`/`cinv`, `ceqHolds_iff_act`,
  `ceqHolds_iff_stab`.
- `AnyK3DColorCensus.lean` — the fast-lane enumeration (mirror of
  `AnyK3DCensusFast`): 8-bit subgroup masks, base-8 gain tuples, the
  twist code used directly (no `negTau`). Cross-checks in
  `AnyK3DColorCensusCount.lean`: `subMasksC_count = 10`,
  `census_count_fastC = 9341248` (288 s) — independently reproduces
  the Python census.
- **Feasibility probe result: ALL 10 subgroups of the color gain group
  are exact-stabilizer realizable** (`monotile/check_color_subgroups.py`
  — brute-force 2-color witnesses on K = 2,3,4 grids, missing = 0). So
  the color census has NO feasibility filter, and the bridge needs only
  "a realized stabilizer is a subgroup" — pure algebra, any K, any T.
- `AnyK3DColorBridge/Part/Complete.lean` — the M3b clone: encoding
  bridge (`gmul8`/`ginv8` `decide`-checked), face equivalence/roots,
  `stabMaskC` (subgroup, no filter, no `1 ≤ K`), class lists/tuple
  index, `cpartOf`, `cprofileMask_eq_union`, membership chain.
- Coverage: `AnyK3DColorVerdictData.lean` (autogenerated;
  `monotile/color_verdict_export.py`) — the unified verdict table:
  all 414,079 canonical profiles tagged 0 periodic / 1 density /
  2 emptyF / 3 emptyI (Python partition-checked; canon 755 ∈ density).
  `AnyK3DColorCoverage.lean` — tier subsequence checks (greedy
  subsequence + membership soundness, no sortedness needed) and
  `colorVerdict_of_mem`: every table profile is `PeriodicRel` or empty.
  `AnyK3DColorCovBase.lean` + 16 `AnyK3DColorCovChunk*.lean` +
  `AnyK3DColorCoverageCheck.lean` — every one of the 9,341,248 census
  masks has a rotation (`permMask g`) in the verdict table, chunked
  `native_decide`s (~85 min across 4-job batches) +
  `mem_censusFastC_covered` decode.

**Gotchas hit (worth remembering):**
- `color_orbits.py` canonicalizes by the LEXICOGRAPHIC min of sorted
  bit-lists, NOT the numeric min of masks (~95% of orbits differ). The
  first coverage formulation (numeric-min `canonOf`) failed because of
  this; the final check avoids canonicalization entirely (any-rotation
  `binMem` into the sorted table).
- A subsequence check is the wrong shape for "9.3M pre-images vs
  414k-entry table" — multiplicities. (The 20 h single-module run that
  evaluated `False` taught both lessons; the serial binMem run took
  ~4.5 h before chunking.)
- Coverage claim externally pre-validated on ALL 9,341,248 raw profiles
  (`monotile/check_color_coverage_full.py`, zero misses).

### R4. Assembly ✅ DONE (2026-08-04)

`AnyK3DColorMain.lean`: `color_census_complete` →
`mem_censusFastC_covered` → `colorVerdict_of_mem` → periodic branch
(`periodic_transport_back`) / empty branch (`tiling_transport` forward
into the verdict's emptiness). Edge cases: K = 0 (vacuous ccompat,
constant field) and T = 0, K ≥ 1 (no decoration exists — `Fin.elim0`).
Structurally the `no_aperiodic_wang_cube_anyK` analogue, with direct
table membership in place of frontier domination.

### R5. Numbers to maintain in the writeup

| tier | profiles | Lean-verified |
|---|---|---|
| empty (density) | 176,197 | ✅ done |
| empty (box UNSAT) | 196,058 | ✅ done (R2: cake-backed axiom + inheritance) |
| periodic | 41,824 | ✅ done (R1) |
| 755 | 1 | ✅ done (density) |
| **total classified** | **414,079** | **414,079 verdicts covered (100%)** |

### R6. Cross-track payoff

The R2(a) in-Lean UNSAT infrastructure also retires the bump/dent track's
`frontierEmptyFacts` axiom (3,371 cheap frontier masks — cake_lpr-external
today), putting `no_aperiodic_wang_cube_anyK` fully inside the kernel too.

## Suggested order

1. ~~R1~~ ✅, ~~R2~~ ✅, ~~R3~~ ✅, ~~R4~~ ✅ — **the color theorem is
   proven** (2026-08-04).
2. **R6** ✅ evidence unified (2026-08-06): all bump/dent trust debt
   (3,371 cheap frontier masks + 387 straggler leaves) re-evidenced
   through the R2 pipeline (`gen_bumpdent_certs.py` →
   `bumpdent_frontier_verified.txt`, 0 failures). The axioms themselves
   stay (in-Lean LRAT checking measured non-viable) unless someone lands
   a faster in-Lean checker.
