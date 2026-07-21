# 2D any-K: THEOREM, machine-checked in Lean (2026-07-16)

**`AnyK2D.no_aperiodic_wang_square` — compiled, axiom-audited:**
`lean-flocq/LeanFlocq/AnyK2D.lean` (+ generated `AnyK2DCerts.lean`).
`#print axioms` = [propext, Classical.choice, Lean.ofReduceBool,
Lean.trustCompiler, Quot.sound] — **kernel + native_decide only; no SAT
solver, no external checker, no input axiom.** `compat_factors` and
`rect_sound` are pure-kernel. Same-day arc: conjectured, empirically
closed, and formally proven 2026-07-16.

Formalization notes: (i) tilings ARE orientation fields by definition, so
the reduction has no stabilizer case analysis — any lift of a physical
tiling works since compat only reads decoration bits; (ii) the theorem
certifies all 1024 equation-masks (superset of the 116 achievable), so no
achievability/K₀ math is in the trust path; (iii) 1024-element Array
literal needs file-wide `set_option maxRecDepth 100000` (whnf of the cons
chain during elaboration of the main theorem, not just the native_decide);
(iv) box-emptiness = ∀ over `Fin w → Fin h → Fin 4` (Fintype-Pi), viable
because every empty relation dies by 3×3 / 1×5.

**Claim (now a theorem):** no aperiodic single-orbit square Wang
tile exists at ANY K — every K-bit-edged square whose C4-rotation orbit
tiles ℤ² admits a fully periodic tiling with period index ∈ {1, 2, 4}
(the element orders of C4).

This is the dress rehearsal for the 3D any-K theorem (`DESIGN-anyk-lean.md`),
Python half done in one session. Every component is machine-validated:

## The chain

1. **Reduction** (tilings of orbit(d) ≅ 4-letter orientation SFT of
   Compat_d): implicitly exact in arena2d's solvers; validated by ZERO
   consistency violations joining relation-level classifications against
   all five exhaustive per-decoration sweeps (K=1..5; includes "every
   unbalanced decoration's relation is empty" — balance law × reduction).
2. **Achievability characterization** (`faceeq2d.py`): Compat is exactly a
   pattern of face equations F_g = ¬(F_h ∘ mirror) — all 10 equations have
   the mirror twist, none identity (2D C4 fact). Achievable assignment ⟺
   gain-graph closure over Z2(mirror)×Z2(sign) has no (0,1) self-gain AND
   no non-held equation implied (coset check). Parity: a forced (1,1)
   self-gain ⟺ even K only. Validated two ways:
   - reconstruction: equations reproduce `compat_tables` exactly on 500
     random decorations (the twist-bookkeeping test);
   - exactness: predicted set == collected set: 99 relations at K≤5, the
     17 predicted extras ALL witnessed at K=6 (`faceeq2d_witness.py`,
     class-representative sampling). **116 canonical relations total; the
     characterization is K-independent, so no K adds more.**
3. **Certificates** (`relations2d.py` + extras classification): all 116
   classified, **87 empty** (box6/box8 UNSAT) + **29 periodic** (torus
   witnesses, index ∈ {1,2,4}) + **0 suspicious**.
4. **Assembly** (the Lean theorem to write): ∀K ∀dec tiles ⟹ Compat_dec
   among the 116 ⟹ per-relation cert ⟹ periodic tiling.

## Files

| file | role |
|---|---|
| `arena2d.py` | geometry, solvers, exhaustive per-K sweeps (K≤6 closed, K=7 running) |
| `relations2d.py` | relation collection/classification + consistency cross-check |
| `faceeq2d.py` | face-equation derivation, reconstruction test, achievability enumeration |
| `faceeq2d_witness.py` | witness search for predicted extras (17/17 at K=6) |
| `relations2d_K{1..5}.json`, `relations2d_K6_extras.json` | the ledger |

## Lean port checklist (next arc)

- [x] 2D reduction — dissolved definitionally (tilings = orientation fields)
- [x] face-equation lemma — `compat_factors` (pure kernel; the 16-case
      `eqHolds_pairIdx` closes by `fin_cases <;> first | rfl | eqHolds_symm`)
- [x] certificates — 1024-mask superset, one `native_decide` (`certs_valid`)
      re-verifies every cert from scratch (Python SAT not in trust base)
- [x] assembly — `no_aperiodic_wang_square (K) (d) : Tiles K d →
      PeriodicallyTiles K d`
- [ ] optional garnish: gain-graph exactness (the 116) + K₀=6 bound as
      standalone math for the paper; Lean↔arena2d data cross-check of the
      geometry conventions at a couple of K values
- [ ] the 3D lift (24 letters, D4 twists, 6 faces) — the real prize

## Open fine print

- Parity split: 29 any-K assignments vs 87 even-only; odd-K achievable set
  stabilizes at 24 canonical by K=5 (whether more appear at K=7 — the
  running K=7 sweep answers; irrelevant to the union, which is fully
  witnessed at K≤6).
- K=6 full-space novelty scan running (expected: exactly the 17 extras,
  nothing else) — final empirical confirmation of stabilization.
