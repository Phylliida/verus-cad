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

Verified so far: **218,021 / 414,079 = 52.6%** of the census.

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

Two sub-problems:

1. **Encoding correctness (proof).** `CNF-UNSAT(box L, held) → ¬∃ BoxTiling
   L (pairOf held)`, hence no ℤ³ tiling via the existing `boxTilingOf`
   restriction. One CNF-satisfiability-to-BoxTiling direction suffices
   (sat ⇒ tiling); the pattern already exists in the bump/dent track
   (`AnyK3DEmptyEnc.lean`) and is reusable.
2. **UNSAT evidence (compute).** Options, in preference order:
   - **(a) In-Lean verified SAT.** The bump/dent M5 probe showed
     `Std.Sat verifyCert` too slow at 43 KB-cert frontier scale — but 3³
     boxes (648 one-hot vars + ~14k clauses) are far smaller. *First task:
     one timed experiment* — export a 3³ CNF + CaDiCaL LRAT cert, check it
     in Lean, measure. If ≲ seconds per profile, batch like the density
     chunks (196k × small certs; chunk by cumulative cert size).
   - **(b) cake_lpr external.** If (a) is too slow: solver untrusted,
     CakeML-verified checker re-checks each LRAT, emptiness stated as an
     axiom with external evidence (same trust profile as
     `frontierEmptyFacts` today). Faster to land, weaker base.
   - **(c) More structural kills.** Bounded exploration: are there other
     arithmetic obstructions (balance-lemma analogues for colors) that
     shrink the SAT set further? Opportunistic only; (a)/(b) is the
     systematic answer.

- Effort: (a) probe 1 day; batch 2–3 days if viable. (b) fallback 1–2 days.
- Risk: cert volume (196k certs, aggregate size) — mitigate by frontier
  reduction (only maximal-empty profiles need certs; subsets inherit via
  `tiling_mono`, as in M4's frontier compression).

### R3. Census completeness (the M3b analogue — biggest proof chunk)

Every color decoration's 84-bit profile is represented in the 414,079
canonical list, up to the rotation group. The Python enumeration
(`color_census.py`) goes through: the gain group of the 8 grid isometries
(+1 signs), its subgroup lattice, set partitions of the 6 faces, and
stabilizer feasibility by brute-force pattern search at K = 2,3,4
(palette-independence for T ≥ 2 follows from K=2 feasibility).

- Sub-deliverables: (i) color decoration type + `compat`; (ii) K-vanishing
  (compat determined by the equation profile — the color analogue of
  `compat_factors`); (iii) the subgroup/partition enumeration verified or
  cross-checked by `native_decide` (objects are small: subgroups of an
  8-element group, stabilizers of K≤4 grids); (iv) canonical-list
  completeness + transport under the 24 rotations (reuse `RotSym`/`relabelO`
  machinery from the bump/dent track).
- Effort: the largest single chunk (M3b took ~6 milestones there).

### R4. Assembly (M5 analogue)

`Tiles d → profile(d) ∈ census (R3) → not empty (R1/R2 cover empties, so
profile is periodic) → PeriodicRelTiles (R1) → PeriodicallyTiles d`
(plus the K=0/K=1 edge cases). Structurally identical to
`no_aperiodic_wang_cube_anyK`; days, not weeks.

### R5. Numbers to maintain in the writeup

| tier | profiles | Lean-verified |
|---|---|---|
| empty (density) | 176,197 | ✅ done |
| empty (box UNSAT) | 196,058 | R2 |
| periodic | 41,824 | R1 (in flight) |
| 755 | 1 | ✅ done (density) |
| **total** | **414,079** | |

### R6. Cross-track payoff

The R2(a) in-Lean UNSAT infrastructure also retires the bump/dent track's
`frontierEmptyFacts` axiom (3,371 cheap frontier masks — cake_lpr-external
today), putting `no_aperiodic_wang_cube_anyK` fully inside the kernel too.

## Suggested order

1. **R1** (lands itself; watch the running export).
2. **R2(a) probe** — one 3³ cert through in-Lean checking, timed. Decides
   (a) vs (b) for 196k profiles and for R6.
3. **R3** in parallel (independent; the long pole).
4. **R4** once R1–R3 exist; **R6** opportunistically after R2(a).
