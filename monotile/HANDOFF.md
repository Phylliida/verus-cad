# monotile HANDOFF (2026-08-03)

For whoever picks this up next. The short version: **every verdict of the
equal-color 3D census is now discharged in Lean** — what remains is the
*representation theorem* (the census is complete) and the final assembly.
Read `PLAN-color-lean.md` first; this file is the operational summary.

## The two tracks

1. **Bump/dent Wang cubes (any K)** — `no_aperiodic_wang_cube_anyK` is
   proven in lean-flocq (`AnyK3DMain.lean`, commit `f6510f4`), modulo one
   declared axiom `frontierEmptyFacts` (externally cake_lpr-evidenced).
   See `RESULT.md`, `DESIGN-anyk-lean.md`, `DESIGN-anyk3d-endgame.md`.
2. **Equal-color Wang cubes (any K, palette ≥ 2)** — the campaign
   classified all **414,079 canonical profiles**: 41,824 periodic,
   372,254 box-empty, canon 755. No aperiodic einstein exists
   computationally; the Lean formalization is underway (this handoff).

## Color track — what's DONE (all in lean-flocq unless noted)

| piece | status | where |
|---|---|---|
| Density lemma (sharp: `(|A|−|B|)·L ≤ 6`) | proven | `ColorDensity.lean` |
| Canon 755 empty by pure counting | proven | `AnyK3DColorDensity.lean` |
| 176,197 empty profiles (density kills) | batch-verified | `AnyK3DDensityCheck.lean` + 12 `AnyK3DDensityKills*.lean` chunks |
| 41,824 periodic profiles (torus witnesses) | batch-verified | `AnyK3DColorPeriodic.lean` (`torusOK`/`torusOK_sound`) + 5 `AnyK3DColorPeriodicData*.lean` chunks |
| 196,058 box-UNSAT profiles | cake-backed axiom + inheritance | `AnyK3DColorEmpty.lean` (+`Check`/`Data`) |
| **414,079 / 414,079 verdicts** | **covered** | |

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

### R3 — census completeness (the long pole, M3b analogue)

Prove that every equal-color decoration's 84-bit equation profile is
represented in the 414,079-entry canonical list (up to the 24 rotations).
Pieces, roughly in dependency order:

1. **Decoration type + compat.** Colors: each face carries a K×K grid of
   palette-≥2 colors; matching = patterns *identical through the twist*
   (bump/dent used complement). Define `CDec T K`, `ccompat`, and prove
   the K-vanishing factorization (compat determined by the 84-bit profile
   — the color `compat_factors`; mirror `AnyK3D.lean` M1).
2. **Achievability enumeration verified.** The Python census
   (`color_census.py`) computed achievable profiles via: the gain group
   of the 8 grid isometries (+1 signs), its subgroup lattice, set
   partitions of the 6 faces, and stabilizer feasibility by brute-force
   pattern search at K = 2,3,4 (palette-independence for T ≥ 2 follows
   from K=2 feasibility — `countclosures.py`). These objects are small
   (subgroups of an 8-element group, K≤4 grids) — plausibly all
   `native_decide`-checkable; the completeness argument needs the same
   proof shape as bump/dent M3b (`census_complete`), NOT a re-enumeration
   of 2^84.
3. **Canonical transport.** Every profile's canonical form is in the
   list, and empty/periodic verdicts transport under the rotation group
   (reuse `RotSym`/`relabelO`/`tiling_transport` from the bump/dent
   track — `AnyK3DTransport.lean`).

### R4 — assembly (days, once R3 exists)

`Tiles d → profile(d) ∈ census (R3) → not empty (Tiling ⇒ SFT nonempty)
→ periodic tier → PeriodicRelTiles → PeriodicallyTiles d`. Structurally
identical to `AnyK3DMain.lean`; include the K=0/K=1 edge cases.

### R6 — cross-track trust debt (opportunistic)

The bump/dent `frontierEmptyFacts` (3,371 cheap masks) already has
cake_lpr evidence (`verify_cheap.py`); it stays an axiom unless someone
lands a faster in-Lean LRAT checker. The color R2 pipeline
(`gen_color_empty_certs.py`) is the template for re-evidencing anything
similar.

## Operational notes (learned the hard way this week)

- **Big Lean data**: split literals into ≤1000-entry sub-arrays and append
  (elaborator stack overflow / heartbeat walls otherwise). Access combined
  data through an `@[irreducible]` index accessor (`frontierJob` pattern)
  — appended-array literals in *unification position* cause unbounded whnf
  blowups; `native_decide`/compiled evaluation is unaffected.
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
  across modules is fine (64 cores here); full cold rebuilds of the batch
  chunks are ~30 min.

## File map (color track)

- `monotile/PLAN-color-lean.md` — the roadmap + tier table (R1/R2 done).
- `monotile/RESULTS-color-density-lemma.md` — the density lemma writeup +
  erratum (sharp bound) + slimming results.
- `monotile/color_density_export.py` → density kill witnesses
  (`color_density_kills.json`, gitignored).
- `monotile/color_periodic_export.py` → torus witnesses
  (`color_periodic_ckpt.jsonl` checkpoint; `color_periodic_witnesses.json`).
- `monotile/gen_color_empty_certs.py` → frontier CNF + cadical + cake_lpr
  (`color_frontier_verified.txt` evidence).
- `monotile/color_empty_lean_export.py` → `AnyK3DColorEmptyData.lean`.
- lean-flocq modules (all committed): `ColorDensity`,
  `AnyK3DColorDensity`, `AnyK3DDensityCheck` + 12 `AnyK3DDensityKills*`,
  `AnyK3DColorPeriodic` + 5 `AnyK3DColorPeriodicData*` +
  `AnyK3DColorPeriodicAll`, `AnyK3DDensityKillsAll`, `AnyK3DColorEmpty`,
  `AnyK3DColorEmptyCheck`, `AnyK3DColorEmptyData`.
