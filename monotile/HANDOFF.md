# monotile HANDOFF (2026-08-04)

For whoever picks this up next. The short version: **the color track is
COMPLETE** — `no_aperiodic_equal_color_wang_cube` is proven in
lean-flocq (`AnyK3DColorMain.lean`): every equal-color Wang cube, any
grid K, any palette T, that tiles ℤ³ admits a fully periodic tiling.
What remains is only cross-track cleanup (R6). Read
`PLAN-color-lean.md` first; this file is the operational summary.

## The two tracks

1. **Bump/dent Wang cubes (any K)** — `no_aperiodic_wang_cube_anyK` is
   proven in lean-flocq (`AnyK3DMain.lean`, commit `f6510f4`), modulo one
   declared axiom `frontierEmptyFacts` (externally cake_lpr-evidenced).
   See `RESULT.md`, `DESIGN-anyk-lean.md`, `DESIGN-anyk3d-endgame.md`.
2. **Equal-color Wang cubes (any K, palette ≥ 2)** — the campaign
   classified all **414,079 canonical profiles**: 41,824 periodic,
   372,254 box-empty, canon 755. **The Lean formalization is now
   complete** (R1–R4 all done, 2026-08-04): the census completeness
   (`color_census_complete`) and the assembly
   (`no_aperiodic_equal_color_wang_cube`) are kernel-checked.

## Color track — what's DONE (all in lean-flocq unless noted)

| piece | status | where |
|---|---|---|
| Density lemma (sharp: `(|A|−|B|)·L ≤ 6`) | proven | `ColorDensity.lean` |
| Canon 755 empty by pure counting | proven | `AnyK3DColorDensity.lean` |
| 176,197 empty profiles (density kills) | batch-verified | `AnyK3DDensityCheck.lean` + 12 `AnyK3DDensityKills*.lean` chunks |
| 41,824 periodic profiles (torus witnesses) | batch-verified | `AnyK3DColorPeriodic.lean` (`torusOK`/`torusOK_sound`) + 5 `AnyK3DColorPeriodicData*.lean` chunks |
| 196,058 box-UNSAT profiles | cake-backed axiom + inheritance | `AnyK3DColorEmpty.lean` (+`Check`/`Data`) |
| **R3** census completeness (any K, any T) | **proven** | `AnyK3DColor{,Gain,Census,CensusCount,Bridge,Part,Complete}.lean` |
| **R3** coverage: all 9,341,248 census masks have a rotation in the verdict table | **kernel-verified** | `AnyK3DColorVerdictData.lean` + `AnyK3DColorCoverage.lean` + `AnyK3DColorCovBase.lean` + 16 `AnyK3DColorCovChunk*.lean` + `AnyK3DColorCoverageCheck.lean` |
| **R4** assembly: `no_aperiodic_equal_color_wang_cube` | **proven** | `AnyK3DColorMain.lean` |
| **414,079 / 414,079 verdicts** | **covered** | |

R3 essentials (details in `PLAN-color-lean.md` §R3): the color census is
re-enumerated Lean-natively with the 8-element gain group; ALL 10 of its
subgroups are exact-stabilizer realizable
(`check_color_subgroups.py`, missing = 0), so there is no feasibility
filter and completeness holds for ANY K and ANY palette T; the count
cross-check `census_count_fastC = 9341248` (native_decide, 288 s)
independently reproduces the Python census. Verdict transport uses the
bump/dent `permMask`/`tiling_transport`/`periodic_transport_back`
machinery unchanged (mask-generic).

Key reusable infrastructure (all proven): `relOfHeld`/`IsTiling`/`Tiles`
(`AnyK3D.lean`), `boxTilingOf` (ℤ³ tiling ⇒ box tiling),
`not_isTiling_of_deficient` (any deficient profile is empty — reusable for
future sweeps), `empty_sound` (CNF UNSAT ⇒ no ℤ³ tiling,
`AnyK3DEmptyEnc.lean`), `tiling_mono`/`periodic_mono` (mask monotonicity,
`AnyK3DCerts.lean`), shown-face geometry tables (`AnyK3DGeom.lean` +
`shownTable` cross-checked 1728/1728).

## Trust base (be honest about it in any writeup)

- **Kernel**: propext, Classical.choice, Quot.sound, plus
  `Lean.ofReduceBool`/`Lean.trustCompiler` from `native_decide` (used for
  all batch/table checks — the project's accepted base).
- **External (TRUST DEBT)**: `colorFrontierUnsat` — 65,250 frontier box
  CNFs are UNSAT; every LRAT cert re-checked by the CakeML-verified
  `cake_lpr` (`monotile/color_frontier_verified.txt`, 0 failures). The SAT
  solver is untrusted. Same trust profile as the bump/dent track's
  `frontierEmptyFacts`. In-Lean `verifyCert` was measured non-viable
  (probe 2026-08-03: stack overflow at default stack, >1 h with 4 GB
  stack, per 214 KB cert; cake_lpr: 0.093 s).

## What REMAINS

### R6 — cross-track trust debt ✅ evidence unified (2026-08-06)

The bump/dent `frontierEmptyFacts` (3,371 cheap masks) and the 34
`stragLeafUnsat` axioms (387 cube-and-conquer leaves) stay axioms
(in-Lean LRAT checking measured non-viable), but ALL of their external
evidence is now re-generated through the R2 color pipeline at one
standard (`gen_bumpdent_certs.py`): fresh `ExportEmptyCNF` exports (the
proven encoder — historical cheap CNFs spot-verified byte-identical,
11/11; straggler bases re-exported since they matched only up to clause
order), cadical `--lrat`, cake_lpr re-check, certs deleted after each
job. Unified ledger: `bumpdent_frontier_verified.txt` — **3,371/3,371
cheap + 387/387 leaves, 0 failures** (~88 min at 4 workers). The axiom
comments in `AnyK3DMain.lean`/`AnyK3DStragTrees.lean` cite it. This
supersedes `cheap_verified.txt` + `strag_verified.txt` (same checker,
older ad-hoc drivers).

## Operational notes (learned the hard way this week)

- **Big Lean data**: split literals into ≤1000-entry sub-arrays and append
  (elaborator stack overflow / heartbeat walls otherwise). Access combined
  data through an `@[irreducible]` index accessor (`frontierJob` pattern)
  — appended-array literals in *unification position* cause unbounded whnf
  blowups; `native_decide`/compiled evaluation is unaffected.
- **Proof-side rewriting around big data**: even `simp only [Array.mem_def,
  List.mem_append]` on a membership in an appended data array whnf-evaluates
  the append chains (deterministic heartbeat timeouts). Use `Array.mem_append`
  rewrites (structural, no data evaluation), or better: generic split lemmas
  (`mem_append5`/`mem_append12` pattern) applied via defeq ascription.
- **Multi-million-scale `native_decide`**: chunk the input list across
  parallel modules (`AnyK3DColorCovChunk*` pattern: one def per slice in a
  base module, one tiny chunk module per slice with its own `native_decide`,
  a decode module bridging `List.mem_iff_getElem` + take/drop). A
  9.3M-mask check measured ~4.5 h single-module; 16 chunks ≈ ~85 min in
  4-job batches. NOTE: this machine crashes with >4 parallel lake jobs —
  batch targets ≤4 per `lake build` invocation (no `-j` flag exists).
- **Canonicalization gotcha**: `color_orbits.py` canonicalizes by the
  LEXICOGRAPHIC min of sorted bit-lists, NOT the numeric min of masks
  (~95% of orbits differ). And subsequence checks are the wrong shape for
  "9.3M pre-images vs 414k-entry table" (multiplicities) — the working
  formulation is any-rotation binary-search membership with early exit
  (`binMem` + `binMemGo_sound`; soundness of "found" needs no sortedness).
- `set_option ... in` breaks if a `/-- -/` doc comment neighbors it; keep
  them adjacent or use file-level options. Big batches: file-level
  `set_option maxHeartbeats` (0 resets to default 200000, it is NOT
  "unlimited").
- Don't create import cycles between data modules and checker modules
  (data files should import nothing).
- Python side: run everything via `./runpy.sh <script.py>` (NixOS
  LD_LIBRARY_PATH dance). `import faceeq3d` rewrites
  `faceeq3d_census.json` (harmless, deterministic). Campaign JSON/JSONL
  data is gitignored; scripts and RESULTS/PLAN docs are committed.
- cadical: `/home/bepis/.elan/toolchains/leanprover--lean4---v4.25.0/bin/cadical`;
  text LRAT needs `--lrat --no-binary`; cake_lpr takes binary.
- Lean builds: `cd lean-flocq && lake build LeanFlocq.<Module>`; parallel
  across modules is fine **up to 4 jobs** (see above); full cold rebuilds
  of the batch chunks are ~30 min.

## File map (color track)

- `monotile/PLAN-color-lean.md` — the roadmap + tier table (R1–R4 done).
- `monotile/RESULTS-color-density-lemma.md` — the density lemma writeup +
  erratum (sharp bound) + slimming results.
- `monotile/color_density_export.py` → density kill witnesses
  (`color_density_kills.json`, gitignored).
- `monotile/color_periodic_export.py` → torus witnesses
  (`color_periodic_ckpt.jsonl` checkpoint; `color_periodic_witnesses.json`).
- `monotile/gen_color_empty_certs.py` → frontier CNF + cadical + cake_lpr
  (`color_frontier_verified.txt` evidence).
- `monotile/gen_bumpdent_certs.py` → R6 unified bump/dent re-evidence
  (`bumpdent_frontier_verified.txt`: 3,371 cheap + 387 strag leaves,
  0 failures).
- `monotile/color_empty_lean_export.py` → `AnyK3DColorEmptyData.lean`.
- `monotile/check_color_subgroups.py` — the R3 feasibility probe (all 10
  subgroups of the 8-element gain group exact-stabilizer realizable).
- `monotile/color_verdict_export.py` → `AnyK3DColorVerdictData.lean`
  (unified 414,079-row verdict table, partition-checked).
- `monotile/check_color_coverage_{sample,full}.py` — external pre-validation
  of the coverage claim (full: 9,341,248/9,341,248, zero misses).
- lean-flocq modules (all committed): `ColorDensity`,
  `AnyK3DColorDensity`, `AnyK3DDensityCheck` + 12 `AnyK3DDensityKills*`,
  `AnyK3DColorPeriodic` + 5 `AnyK3DColorPeriodicData*` +
  `AnyK3DColorPeriodicAll`, `AnyK3DDensityKillsAll`, `AnyK3DColorEmpty`,
  `AnyK3DColorEmptyCheck`, `AnyK3DColorEmptyData`, `AnyK3DColor`,
  `AnyK3DColorGain`, `AnyK3DColorCensus` + `AnyK3DColorCensusCount`,
  `AnyK3DColorBridge`, `AnyK3DColorPart`, `AnyK3DColorComplete`,
  `AnyK3DColorVerdictData`, `AnyK3DColorCoverage`, `AnyK3DColorCovBase`
  + 16 `AnyK3DColorCovChunk*`, `AnyK3DColorCoverageCheck`,
  `AnyK3DColorMain`.
