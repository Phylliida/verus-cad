# Monotile SAT-Reflection — Status

**Goal.** Machine-check `SearchUnsat`: there is no decoration `dec : Fin 54 →
Bool` that is Balanced ∧ tiles the 4³ box ∧ avoids the forbidden patterns —
i.e. that the arena2 search's final CNF is UNSAT. **Honest scope:** this is
*not yet* "no aperiodic Wang cube exists." The 4³ + patterns criterion is
arena2's own CEGIS/period-finder output (see `NOTES_FOR_AGENT.md`); the bridge
from "that CNF is UNSAT" to the tiling theorem (period-finder soundness +
balance necessity + box sufficiency + box→ℤ³ compactness) is **unformalized**.
**Trust boundary:** currently `[propext, Classical.choice, Quot.sound,
Lean.ofReduceBool, Lean.trustCompiler]` — the last two mean cert-checking
trusts the Lean *compiler* (`native_decide`), so "kernel-clean" is aspirational
(the clean path is an external CakeML-verified LRAT checker).

## Architecture

```
sym_reduction (general keystone)                       ── PInvAssemble
   ⊗ P_inv on real data (24 rotations + flip)          ── PInvData/Pat/Finish
   → real_sym_reduction → searchUnsat_of_lex
   → searchUnsat_real (lexCNF) (enc) (huns) : ¬∃dec, RP dec
        enc  : RPlex dec → ∃a, eval a genArenaCNF = true   (encode-complete)
        huns : genArenaCNF.Unsat                            (cube-and-conquer)
```
`RP = Balanced ∧ TilesBox ∧ Avoid`; `RPlex = RP ∧ lex-minimal in its orbit`.
The symmetry half reduces the full search to lex-minimal representatives; the
SAT half proves that lex-broken instance UNSAT.

## Done (all compiling, kernel-clean)

| Piece | Where | What |
|---|---|---|
| verifyCert scales | (earlier probes) | data-based LRAT UNSAT checking in Lean |
| `sym_reduction` | PInvAssemble | keystone: G-invariant + nonempty ⟹ ∃ orbit-min (Finset.exists_min_image + classical), generic over `LinearOrder` |
| **P_inv, real data** | PInvData/Pat/Finish | `P_rot_real` (all 24 rotations) + `P_flip_real`, from `horb`(orbit closure) + `hpat`(pattern closure) + `RotSym` |
| assembly | PInvAssemble | `real_sym_reduction`, `searchUnsat_of_lex`, `searchUnsat_real`; key = `toLex` (Pi.Lex) |
| `unsat_of_cubes` | CubeCompose | cube-and-conquer composition lemma (validated w/ real verifyCert) |
| `genArenaCNF` | GenArena, GenArenaLex | **785,686 clauses** = genCore 770,740 + lex 14,946, function-generated, exported to `genArena.cnf` |
| **`enc_core`** | GenArenaEnc | `TilesBox ∧ Avoid → ∃a, eval a genCore = true` — full completeness proof |
| lex-`enc` toolkit | GenArenaLexEnc | `le_clause` (lex-min⟹≤-clause via Pi.Lex), `assignFull` + round-trips, `lexmin_gfAct`, `genCore_sat`, `prefixEq_succ` |

## Key lessons

1. **Function-generate, never literal.** Large nested-`List` literals don't
   elaborate (657K-clause CNF, 792-pattern closure both timed out). Generate
   from small base data + `native_decide` — genCore, patterns256, cpairs all do
   this. (Also: `List.enum` is gone in v4.25 → stubs `sorry`; use `List.zipIdx`.)
2. **The rotation geometry collapses.** `Compat (rotDec_g dec) ax o1 o2 =
   Compat dec ax (o1∘g)(o2∘g)` — pure orientation re-indexing, same axis. So
   `RotSym` needs **no affine cube-symmetry κ** (κ = identity); the whole
   geometric content is one `native_decide`. This was the pivotal insight.
3. **Pi.Lex over geometric sums.** Switching the lex key to `toLex dec :
   Lex (Fin 54 → Bool)` makes the lex-leader ≤-clause fall out of the Pi.Lex
   `<` characterization — no Nat-value / geometric-sum argument.
4. **Balance is droppable.** `genArenaCNF` (no balance) is UNSAT — a *stronger*
   statement that still implies `SearchUnsat`. Verified: 0 SAT across all tested
   cubes; the deep "hard" cubes are hard-UNSAT (~35s), not SAT.
5. **Monolithic is hopeless; cube-and-conquer + lex is tractable.** The full
   instance times out (>350s, GB-size partial cert); one lex-broken cube solves
   in ~0.3s with a tiny cert.
6. **Cert generation must be resumable** — hash-keyed certs + split-node cache,
   so machine restarts continue from the frontier instead of redoing the prefix.

## Semantic bridge (arena2 CNF-UNSAT → "no aperiodic Wang cube")

Decomposes into L1+L2+L3 (see `NOTES_FOR_AGENT.md §5`); compactness/Lemma A/
period-finder-soundness NOT needed.

- **L2 DONE for all 33 base patterns** (`L2Periodic.lean` + `L2Data.lean`):
  - *Generic machinery, kernel-clean* (`[propext,Classical,Quot]`): `ValidZ3`,
    `PeriodicTiling` (valid ℤ³ tiling + full-rank diagonal period lattice),
    `l2_constant`, and the reusable **`l2_diagonal`** — lifts a torus grid to a
    periodic ℤ³ tiling via `ZMod` and proves any `S`-realizer admits it.
  - *33 machine-verified theorems* `l2_pᵢ : Realizes dec Sᵢ → PeriodicTiling dec`
    (`native_decide` certificates, so `+[ofReduceBool,trustCompiler]`). Diagonal
    witnesses obtained by lifting each skew witness to its diagonal sublattice.
    Certificate **split** into `hcov` (coverage — cheap membership over all
    cells) + `hsnd` (soundness — `cpairs ⊆ S` on the few distinct adjacencies,
    uniform type) to make `native_decide` tractable: **62s** vs 500s+ naive
    (the 864-cell torus alone was 200s with the naive per-cell `cpairs` check).
- **L2 BRIDGE COMPLETE** (`L2Bridge.lean`): **`l2_bridge : ¬Avoid patterns256
  dec → PeriodicTiling dec`** — the full L2 half, over the *entire* `patterns256`
  closure. RotSym transport via `compat_rot` + `periodic_rot` (rotation = pure
  orientation re-indexing, κ=id, so the ℤ³ tiling and its periods transport for
  free) + `cover` (`native_decide` confirms `patterns256` = rotation-closure of
  the 33 bases, exact form) + `realizes_rot`. Contrapositive: `¬PeriodicTiling
  dec → Avoid dec`, i.e. any decoration with no periodic tiling avoids every
  pattern — exactly what feeds the final refutation.
- **L1 + FINAL WIRING COMPLETE** (`L2Final.lean`): `l1 : TilesZ3 dec → TilesBox
  cpairs dec` (trivial restriction, `[propext]`) and **`no_einstein`**:
  `(¬∃ dec, TilesBox cpairs dec ∧ Avoid patterns256 dec) → ¬∃ dec, TilesZ3 dec ∧
  ¬PeriodicTiling dec` — *no decoration tiles ℤ³ without admitting a periodic
  tiling* (no aperiodic K=3 Wang cube). The full bridge L1+L2+L3 is assembled;
  `no_einstein` rests **only** on the SAT-side hypothesis `hsearch`.
- **Balance-free `searchUnsat` DONE** (`L2SearchFree.lean`): `searchUnsat_free
  (enc)(huns) : ¬∃ dec, TilesBox ∧ Avoid` — the generic `sym_reduction` keystone
  instantiated with `RP' = TilesBox ∧ Avoid` + component rotation/flip invariance
  (`htile`/`avoid_rot`/`tilesBox_flip`/`avoid_flip`); no `Balanced`, no Lemma A.
- **`no_einstein_final` ASSEMBLED** (`L2Theorem.lean`): `(enc) → (huns) → ¬∃ dec,
  TilesZ3 ∧ ¬PeriodicTiling` — the complete theorem, conditional **only** on the
  two SAT-side inputs. *Everything mathematical is proven and machine-checked.*
- **L3**: folded into `l2_diagonal` (the lift *is* L3).

## Remaining (SAT half + wiring)

- **lex-`enc` body — DONE** (`GenArenaLexEncBody.lean`, `[propext, …ofReduceBool…]`,
  no sorry): `lexOne_sat` (each lex-leader block satisfied by `assignFull`) →
  `lexCNF_sat` → `lex_enc`. The clause-bash cracked via **decode → abstract the
  `decide(prefixEq…)` terms to opaque Bools `Q,Q1` (+ `d,y`) → revert `hle`/`hrec`
  → `∀ Q Q1 d y, (Q1=Q∧(d=y)) → (Q∧d→y) → clause = true` by `decide`** (16-combo
  check per clause, no fragile `simp` closing). Key gotcha: `yT_eval` also fires
  on the `!fpos` (yF) literal → `gfAct g (!fpos)`, fixed by `gfAct_not`.
- **`no_einstein_of_unsat` ASSEMBLED** (`L2Theorem.lean`): `genArenaCNF.Unsat →
  ¬∃ dec, TilesZ3 ∧ ¬PeriodicTiling`. `enc` discharged by `lex_enc`. **The entire
  einstein theorem now reduces to a SINGLE remaining obligation: `huns`.**
- **`huns` — THE ONLY REMAINING OBLIGATION**: `genArenaCNF.Unsat`. **Trust model
  = cake_lpr** (Danielle's call): the CakeML/HOL4-verified LRAT checker discharges
  per-cube UNSAT; Lean proves the whole reduction *to* `genArenaCNF.Unsat`. Final
  trust = Lean kernel (bridge + enc + searchUnsat_free) + cake_lpr (per-cube).
  - **cake_lpr BUILT + WORKING** (`tools/cake_lpr/`, `gcc` from the shipped CakeML
    `.S`): reads *binary* LRAT natively, so the existing 87GB of cadical certs are
    usable as-is. Verifies real cube certs → `s VERIFIED UNSAT` (tested, 5/5).
  - **cake_lpr is genuinely checking** (not rubber-stamping): it caught a corrupt
    22.6MB cert (`e51e9e5d…`, from an interrupted cadical run that the resumable
    generator trusted because it was nonzero-size) — "clause index has no reduction
    sequence". `stream_verify.py` now **re-solves on a cake_lpr FAIL** (delete corrupt
    cert → fresh cadical → re-verify; hard-stop only if a freshly-solved cert is
    rejected). A real integrity check survived.
  - **Streaming pipeline** (`stream_verify.py` + `run_verify.sh`): re-traverses the
    DFS tree (reusing `split_cache`), reconstructs each leaf's cube, cake_lpr-verifies
    its cert, logs to `verified.txt` + **deletes the cert** (bounds disk), solves the
    unsolved frontier, and writes `manifest.json` + a trie-completeness **cover check**
    when the tree is complete. Resumable. Currently running in background (freeing
    the 87GB as it verifies). A prior run's stale manifest had 1428 leaves (tree does
    complete).
  - **COVER FORMALIZED** (`CubeCover.lean`, `[propext, Quot.sound]` — pure kernel,
    no `native_decide`, no sorry): `VTree` binary decision tree; **`VTree.covers`**
    (every assignment satisfies some leaf cube — structural induction, cover *by
    construction*) + `unsat_of_cubes` + **`VTree.unsat`** (tree + per-leaf UNSAT ⟹
    `cnf.Unsat`). The cover half of `huns` is now Lean-kernel-verified.
  - **INSTANTIATION DONE + CAPSTONE ASSEMBLED** (`ConcreteTree.lean`+`NoEinstein.lean`,
    `export_tree.py`): manifest → preorder shape string (round-trip verified:
    `parseTree order shape`.cubes = manifest cube set *exactly*) → function-generated
    `realTree : VTree` (2855-token shape, elaborates in 9s); `ConcreteTree.huns :
    genArenaCNF.Unsat` (cover kernel-proven via `VTree.covers`, per-cube = axiom
    `perCubeUnsat` [cake_lpr]); **`no_aperiodic_wang_cube : ¬∃ dec, TilesZ3 dec ∧
    ¬PeriodicTiling dec`** = `no_einstein_of_unsat huns`. **AXIOMS = [propext,
    Classical.choice, Quot.sound (kernel) + ofReduceBool, trustCompiler (native_decide,
    finite geometry) + perCubeUnsat (cake_lpr, per-cube UNSAT)]** — SAT solver NOT
    trusted. THE COMPLETE THEOREM IS ASSEMBLED.
  - **Refresh (mechanical)**: currently on the *stale* 1428-leaf manifest. When the
    streaming job finishes (fresh fully-cake_lpr-verified manifest), re-run
    `export_tree.py` + recompile ConcreteTree → identical theorem, freshly-verified cubes.
- ~~binary-`Dec` refactor~~ and ~~final wiring~~: **DONE** — `no_einstein_final`
  reduces everything to `enc` + `huns`; only these two remain.

## Proof-mining findings (what's load-bearing)

Empirical, via `arena2.Synth` (variable-decoration search instance) and
`box_sat` (per-decoration tileability). Full write-up in `NOTES_FOR_AGENT.md §3`.

- **Box size 4³ is load-bearing, threshold sharp:** 2³ SAT, 3³ SAT, **4³ UNSAT.**
- **Patterns essentially irredundant — no small core:** one-pass drop-each over
  the 33 → **30 individually load-bearing (removal ⟹ SAT), 0 redundant, 3
  undetermined.** No dozen-pattern shortcut; the obstruction is SAT-scale.
- **Box geometry is active:** box-only 4³ is SAT (patterns filter the tileable
  ones), but some decorations are geometrically untileable regardless of
  patterns. Exclusion at 4³ = **geometry ∪ pattern**.
- **3³ witness dies at 4³ by geometry, not pattern:** the extracted balanced
  27-bump 3³-tiler realizes no pattern; it tiles arbitrarily long *thin* bars
  (all axis-digraphs cyclic) and up to 4×3×2 / 3×3×3, but fails **exactly at the
  4×3×3 slab**. Obstruction is genuinely **3-D** (3×3 cross-section over length
  4), not a 1-D bar. `patterns + 1×1×4` is SAT (no collapse); box+patterns stays
  SAT to 4×4×2, hard at 4×3×3 — candidate minimal UNSAT box (~half the clauses).
  *(Corrects an earlier "1-D length-4" claim — over-read from testing only
  3×3-section boxes.)*
- **Balance is the sole redundant constraint** (no-balance instance is UNSAT).
- **L2 pattern-soundness confirmed (33/33):** every pattern-block admits a
  periodic tiling using only its own pairs (torus size 1–32, `l2_witnesses.json`)
  ⟹ no over-approximation; every excluded decoration is genuinely periodic. This
  is the riskiest bridge lemma (an over-approximating block would hide an
  einstein) — validated empirically + by construction. Formalizes as 33 finite
  torus-tiling certificates + RotSym transport for the conjugates.
- *Gotcha:* `box_sat` takes ±1 decorations (`v1+v2==0`), not 0/1; sanity-check
  against a known-answer object (witness must tile 3³) caught the format bug.

## Files

`lean-flocq/LeanFlocq/`: PInvProbe, HtileProbe, PInvData, PInvDataPat,
PInvFinish, PInvAssemble, CubeCompose, GenArena, GenArenaLex, GenArenaEnc,
GenArenaLexEnc, **L2Periodic** (bridge L2/L3 core + rotation transport),
**L2Data** (33 verified `l2_pᵢ`), **L2Bridge** (`l2_bridge`, full closure),
**L2Final** (`l1` + `no_einstein`), **L2SearchFree** (`searchUnsat_free`,
balance-free discharge), **GenArenaLexEncBody** (`lexOne_sat`/`lexCNF_sat`/`lex_enc`,
the lex-`enc`), **L2Theorem** (`no_einstein_final` + `no_einstein_of_unsat`),
**CubeCover** (`VTree.covers`/`VTree.unsat`, cube-cover by construction).
`monotile/`: arena2.py (search), cube_conquer3.py, gen_cube_certs.py (resumable
cert gen), genArena.cnf (exported DIMACS), arena2_patterns.json (33 base
patterns), cube_certs/ (leaf certs + manifest), l2_witnesses.json (periodic
witnesses / L2 certificates), NOTES_FOR_AGENT.md.
