# DESIGN: the 3D any-K Lean endgame (M3b, M4, M5) — v1.0

Status snapshot (2026-07-17): M1 (`AnyK3D.lean` + generated `AnyK3DGeom.lean`),
M2 (`AnyK3DGain.lean`, pure kernel), M3-core (`AnyK3DCensusFast.lean`,
`census_count_fast : censusFast.size = 1445865` by native_decide) all
compiled and audited. Frontier computed: 3,405 maximal-empty + 340
minimal-periodic (`anyk3d_frontier.json`), 340/340 rect torus certs
(`anyk3d_periodic_certs.json`, dims ≤ 12³). This document specifies every
remaining theorem, proof strategy, and data artifact to reach

    theorem no_aperiodic_wang_cube_anyK (K : ℕ) (d : Dec K) :
        Tiles K d → PeriodicallyTiles K d

## 0. Pre-flight decisions (Python, do FIRST — they shape M4)

**P1. Frontier route decision.** The frontier was computed over the 66,134
CANONICAL masks, but `censusFast` holds all 1,445,865 raw profiles. A raw
empty profile need not be ⊆ a *canonical* maximal-empty. Two routes:

- **Route A (recommended): canonical frontier + rotation transport.**
  Coverage statement: every census mask, after one of the 24 equation
  permutations, is dominated by the canonical frontier. Needs the eqperm
  table (24×84, from `orbits3d.py` — validated there by 30×24 exact
  transport checks) as Lean data, and the M4.4 transport lemma. Cert count
  stays 3,405 + 340.
- **Route B: raw frontier, no transport.** Recompute antichains over all
  1.4M (Python; popcount-bucketed to avoid n²). Expect ≤ 24× growth
  (~80k empty / ~8k periodic). Torus certs for the extra periodic elements
  are free (rotate the 340 grids in Python), but ~80k LRAT empties ≈ 4GB —
  forces the external cake_lpr route. More data, less math.

Decide by: computing the raw-frontier sizes (30-min Python job). If raw
maximal-empty ≲ 15k AND cert sampling (P2) is small, Route B becomes
tempting; otherwise Route A. Default: **Route A**.

**P2. Empty-cert sizing.** Generate LRAT certs for ~30 sample maximal-empty
masks (per-mask CNF: box up to 6³ = 216 cells × 24 one-hot ≈ 5.2k vars,
~100-150k clauses; `cadical --lrat`). Measure sizes. Thresholds:
- avg ≤ 30KB → total ≈ 100MB → **chunked in-Lean verifyCert** viable
  (~50 generated files of ~2MB string data; `Std.Tactic.BVDecide.Reflect.
  verifyCert` + native_decide per chunk — trust stays kernel+native).
- avg > 30KB → **cake_lpr streaming** (the K=3 pipeline verbatim: generate
  → check → record → delete; one external axiom `frontierEmpty` listing
  the 3,405 facts; trust = K=3's profile).
Also try smaller boxes per mask first (most empties die at 3³-4³ — the
campaign tiers say ~99% at ≤4³) — certs shrink accordingly; only the
box5/box6 stragglers (53 canonical) have big CNFs.

**P3. dedupSorted provability check.** M3b's membership chain needs
`x ∈ a → x ∈ dedupSorted a`. Check whether the Batteries/Lean core API has
`Array.qsort` permutation/membership lemmas. If NOT (likely):
refactor `dedupSorted` to `List.mergeSort`-based (core, csimp-tail-safe,
has `List.mergeSort_perm`) + an Array-push dedup fold (tail-safe, easily
characterized: `mem_dedup_fold : x ∈ l.foldl f #[] ↔ x ∈ l` for the
adjacent-dedup fold over a SORTED list — prove via sorted-adjacent
reasoning or just prove the ⊇ direction which is all we need).
⚠ Refactoring `dedupSorted` INVALIDATES `census_count_fast` — rerun that
native_decide (≈40-60 min) after the refactor, BEFORE building M3b on it.

## 1. M3b — completeness: `census_complete`

    theorem census_complete (K : ℕ) (hK : 1 ≤ K) (d : Dec K) :
        profileMask (heldOf K d) ∈ censusFast.toList

with `profileMask (hs : Fin 84 → Bool) : ℕ :=
(List.finRange 84).foldl (fun acc i => if hs i then acc ||| (1 <<< i.val)
else acc) 0`.

New file `AnyK3DBridge.lean` (imports Gain + CensusFast). Sub-lemmas in
build order:

**B1. Bit-reading lemmas** (pure Nat, no geometry):
- `testBit_profileMask : (profileMask hs).testBit i ↔ hs ⟨i, _⟩` for i < 84,
  and `.testBit i = false` for i ≥ 84. Proof: foldl-induction with the
  invariant "acc's bits below the processed index are decided, above are 0".
  Reusable helper: `foldl_or_shift` characterizing bit-accumulation folds.
- Same shape for `classMask`: `(classMask re idx H).testBit i ↔ ∃ entry ∈
  re, entry.1 = i ∧ heldBit-condition` — the relEqs entries have distinct
  bit indices (they come from a filterMap over range 84 — provable
  distinctness, or restate with a lookup formulation).
- `Nat.eq_of_testBit_eq` finishes mask equalities.

**B2. Encoding bridge** (connect encoded arithmetic to M2's Gain):
- `gmul16_encG : gmul16 (encG a) (encG b) = encG (gmul a b)`
- `ginv16_encG : ginv16 (encG a) = encG (ginv a)`
- `negTau_encG : negTau t.val = encG (t, true)`
- `encG_lt : encG w < 16`, `decG_encG : decG (encG w) = w`
All finite: prove by `decide` (16², 16, 8 cases — kernel-fast).

**B3. The face equivalence and its structure:**
- `related d g h := ∃ w : Gain, d g = actF w (d h)`.
- `related_refl/symm/trans` — one-liners from `actF_one`, `actF_inv_actF`,
  `actF_actF`.
- `rootF d g : Fin 6` := minimum of the (nonempty, decidable) Finset
  `{h | related d h g}` via `Finset.min'`. Lemmas: `related_rootF`
  (rootF related to g), `rootF_eq_of_related`, `rootF_le`,
  `rootF_rootF = rootF` (root is its own root, and rootF (rootF g) = rootF g).
- Class of g: `cls g := (List.finRange 6).filter (rootF d · = rootF d g)`
  — a sorted list with head = rootF (min). Lemma: `head_cls = rootF`.
- The partition: `partOf d : List (List ℕ)` := the distinct classes in
  root order, faces as ℕ (`.val`-mapped, sorted ✓ filter over finRange).

**B4. `mem_partitionsN`** (the combinatorial lemma):
    theorem mem_partitionsN (P : List (List ℕ)) :
        SortedPartitionOf P l → P ∈ partitionsN l
  where `SortedPartitionOf` = classes nonempty, sorted, heads sorted?, and
  their multiset-union = l. Prove by induction on l mirroring the
  enumerator: l = x :: rest → x is the head of its class (x = min of l);
  remove it; the残り is a SortedPartitionOf rest; the insertion branch
  (`part.set i (x :: block)` or `[x] :: part`) reconstructs P. Est. 60-100
  lines; the fiddliest pure-list lemma of the plan. Mitigation if painful:
  reformulate `partitionsN` as "all functions Fin 6 → Fin 6 collapsed to
  label-partitions" (labelings are trivially complete: label g := rootF g)
  — costs a rerun of census_count_fast (enumerator change: 6^6 = 46,656
  labelings instead of 203 partitions with duplicate profiles deduped —
  ~230× more enumeration work: rerun ≈ hours; acceptable overnight).

**B5. Gains and the tuple index:**
- For each class, classical-obtain gains w_j with `d (member j) = actF w_j
  (d root)`, w_0 := (0, false) explicitly.
- `idx := Σ_{j≥1} encG w_j · 16^(j-1)`; digit lemma
  `gainAt_digits : gainAt idx j = encG w_j` (j ≥ 1, digits < 16):
  bespoke induction on the digit list (base-16 positional extraction;
  ~30 lines) plus `gainAt idx 0 = 0 = encG (0,false)` (definitional).
- `idx < 16^(m-1)` from digit bounds.

**B6. Stabilizer mask:**
- `HM := (List.range 16).foldl (fun acc n => if actF (decG n) (d root) =
  d root then acc ||| (1 <<< n) else acc) 0`.
- `HM.testBit n ↔ actF (decG n) (d root) = d root` (B1-style).
- `isSubgroupM HM = true` — from actF algebra (identity, gmul-closure via
  actF_actF, ginv-closure via cancellation) + B2 bridges.
- `feasibleM HM = true` — from `realized_stab_feasible` (hK : 1 ≤ K):
  bits 1, 9, 15 are encG of (0,true),(4,true),(7,true) ✓ excluded.
- `HM ∈ subMasks.toList` — HM < 65536 + the two filters ⟹ mem of
  List.filter (List.range 65536).

**B7. The profile equality** (the keystone):
    profileMask (heldOf K d) =
      (partOf d).foldl-union of classMask (relEqs cls) idx_cls HM_cls
  Per equation bit i (via B1 + `Nat.eq_of_testBit_eq`):
  - same-class case: `eqHolds_iff_stab` (M2) + B2 + B6 testBit ⟺ the
    classMask condition; the relEqs entry exists with the right member
    positions (idxOf? on the sorted class list — lemma connecting
    `members.idxOf? (efa i)` to the chosen ordering).
  - cross-class case: eqHolds ⟹ related via (eta i, true) ⟹ same root —
    contradiction; and no relEqs entry (idxOf? = none on one side) ⟹ bit
    unset in every class mask.

**B8. Membership chain:**
- `mem_classOptionsFast : HM ∈ subMasks.toList → idx < 16^(m-1) →
  classMask re idx HM ∈ (classOptionsFast members).toList` — foldl-push
  accumulation lemma + dedupSorted-⊇ (P3).
- `mem_censusFast : part ∈ partitionsN → (∀ cls, chosen mask ∈
  classOptionsFast cls) → union ∈ censusFast.toList` — flatMap/foldl
  induction over the class list + dedupSorted-⊇.
- Compose B3-B8 → `census_complete`. 

Effort: B1-B2 half a session; B3-B6 one session; B7 one session; B4+B8
one session (B4 is the wildcard). Total est. **3-4 focused sessions**.

## 2. M4 — certificates

New files: `AnyK3DFrontier.lean` (generated data: maxEmpty, minPeriodic,
eqperm), `AnyK3DPeriodicCerts.lean` (generated: 340 × (mask, dims, grid
base-24 Nat — largest 12³ = 1728 digits ≈ 2.4KB numeral; total ~300KB)),
`AnyK3DCerts.lean` (theory).

**C1. Monotonicity lemmas** (easy, pure):
- `relOfMask` : ℕ → Rel (mask → relation via tEq lookup — align with
  relOfHeld∘maskBits).
- `rel_mono : m ⊆ m' (bitwise) → ∀ ax o1 o2, relOfMask m ax o1 o2 = true →
  relOfMask m' ax o1 o2 = true`.
- `tiling_mono : IsTiling (relOfMask m) ω → m ⊆ m' → IsTiling (relOfMask
  m') ω` (pointwise). Corollaries: periodic-monotone ↑, empty-antitone ↓.

**C2. Torus soundness (3D rect engine):**
- `gLet3 grid b c x y z : Fin 24` (base-24 digit), `rect3OK` checker
  (List.range triple loop, wrapped adjacency, all three axes).
- `rect3_sound : rect3OK R a b c grid = true → ∃ ω, IsTiling R ω ∧ three
  axis periods` — the 2D `rect_sound` proof with a third component;
  reuse/duplicate `emod_lt'`, `emod_shift_nat` (already proven twice in
  the codebase — consider a tiny shared `EmodLemmas.lean`).
- ONE native_decide: `periodic_certs_valid : ∀ i < 340, rect3OK
  (relOfMask (minPeriodic[i])) dims[i] grid[i] = true` (concrete data
  scan; est. < 1 min native).

**C3. Empty soundness:**
- `box3OK` (3D box validity, Prop over Fin w → Fin h → Fin dp → Fin 24)
  + `boxOK_of_tiling` restriction (2D pattern + third axis).
- CNF layer: `emptyCNF (m : ℕ) (dims) : CNF Nat` generated in Lean
  (one-hot + compat clauses from relOfMask — the SatReflection encode
  pattern; ~80 lines) + `encode_complete : box3OK f → satisfying
  assignment` (the 2026-06-15 probe proofs, one-hot + binary-compat case
  only — NO e-vars/balance/lex here, the easiest instance of that
  machinery).
- Per-mask UNSAT: per P2's decision either
  (a) `verifyCert (emptyCNF m dims) certString = true` by native_decide,
  chunked ~70/file, or (b) external axiom `frontierEmptyFacts` with the
  cake_lpr manifest (K=3 `ConcreteTree` pattern).
- `empty_sound : [UNSAT fact] → ¬∃ ω, IsTiling (relOfMask e) ω` via
  boxOK_of_tiling + encode_complete.

**C4. Rotation transport (Route A):** — **REPLACED 2026-07-20 (see note).**
- Data: `eqperm : Array (Array ℕ)` (24×84, exported from orbits3d).
- `permMask g m` bitmask reindex.
- The semantic lemma (K=3 `PInvFinish` shape, orientation-reindex only):
  `transport : IsTiling (relOfMask m) ω → IsTiling (relOfMask (permMask g
  m)) (ω transported)` where the transported field composes the spatial
  rotation (permuting/negating ℤ³ coordinates) with the orientation map
  o ↦ gmap_g(o). Load-bearing finite fact (native_decide on the triple
  tables + eqperm data): the conjugation identity relating
  relOfMask(permMask g m)(ax, o1, o2) to relOfMask m applied to
  transformed triples. Periodicity transports (lattice conjugates —
  axis-aligned periods map to axis-aligned periods since the rotations
  permute±negate axes ✓ stays in the three-axis-period form).
- Coverage native_decide:
  `census_covered : ∀ m ∈ censusFast, ∃ g < 24, (∃ q ∈ minPeriodic,
  q ⊆ permMask g m) ∨ (∃ e ∈ maxEmpty, permMask g m ⊆ e)`
  (compute: 1.4M × ≤24 × (340 + 3,405 with short-circuit) — est. minutes;
  if slow, precompute per-mask canonical form first inside the checker).

> **2026-07-20 — C4 DONE, and much simpler than this sketch.**
> Ground-truthing the conjugation identity in Python (monotile/check_conj*.py)
> showed: (1) the identity as sketched above (spatial rotation + gmap)
> FAILS for orbits3d's eqperm (36,288/41,472 mismatches) — that eqperm is
> the *decoration-conjugation* action, not a tiling-rotation action;
> (2) the correct transport needs **no spatial rotation at all**: rotating
> the decoration relabels orientations by right multiplication,
> `compat (rotDec g d) ax o1 o2 = compat d ax (o1·g) (o2·g)`, verified
> `EQPERM[g][teq(ax,o1,o2)] = teq(ax, rmul[g][o1], rmul[g][o2])` for all
> 41,472 triples. So `permMask` uses eqperm (consistent with the census
> canonicalization ✓), the transported field is `r_g⁻¹ ∘ ω` (pointwise
> relabeling), and periods transport *identically* — the "axis negation"
> risk is gone. Landed in `AnyK3DTransport.lean` (`epAt_teqN` by
> native_decide; `tiling_transport`, `periodic_transport`,
> `permMask_inv`, `periodic_transport_back`) with data in
> `AnyK3DFrontier.lean` (`eqperm`, `rmul`, `rotInv`).

Effort: C1 trivial; C2 one session; C3 1-2 sessions + the cert campaign
(generation is a Python overnight; validation one native_decide per
chunk); C4 1-2 sessions (the transport lemma is the substantial one).

## 3. M5 — assembly (`AnyK3DMain.lean`)

    theorem no_aperiodic_wang_cube_anyK (K : ℕ) (d : Dec K)
        (h : Tiles K d) : PeriodicallyTiles K d

Proof skeleton:
- `K = 0`: compat is all-true (eqHolds vacuous over Fin 0) — lemma
  `compat_zero : compat 0 d = fun _ _ _ => true` by decide-per-triple? No:
  eqHolds at K=0 is `decide (∀ p : Fin 0 × Fin 0, …) = true` definitional.
  Constant ω := fun _ => 0 is a tiling with periods (1,1,1). Done.
- `K ≥ 1`: `census_complete` → `census_covered` at m := profileMask
  (heldOf K d) → obtain g and the branch:
  - periodic branch: q ⊆ permMask g m; `periodic_certs_valid` + `rect3_sound`
    give a periodic tiling for relOfMask q → `tiling_mono` lifts to
    permMask g m → `transport` (inverse rotation) back to relOfMask m →
    rewrite `relOfMask m = relOfHeld (heldOf K d) = compat K d` (mask/held
    correspondence + `compat_factors`). Done.
  - empty branch: permMask g m ⊆ e; from h obtain ω for compat = relOfMask
    m → transport to permMask g m → tiling_mono into relOfMask e →
    contradiction with `empty_sound e`. (Note: empty branch needs transport
    FORWARD, periodic branch needs it BACKWARD — prove transport for all g
    with inverses available, or state it as an iff.)
- Mask/held correspondence: `relOfMask (profileMask hs) = relOfHeld hs`
  (B1 bit lemmas + teq bounds).

Effort: half a session once M3b/M4 exist.

## 4. anyk-03 — the formal K=2 closure (independent track)

Inputs ready: `k2_static.cnf`, the 151-cube tree (`cube_k2_done.jsonl`),
8 point-refutations (anyk-01). Steps: (1) per-leaf DIMACS = base CNF +
cube units; cadical --lrat each (tiny); stream through cake_lpr
(gen_cube_certs pattern, paths parameterized for K=2); (2) cover-by-
construction tree (reuse `CubeCover.lean` verbatim — it is
instance-agnostic); (3) the 8 point-block box-UNSAT certs (5³/8³ boxes);
(4) instantiate the K=3 `ConcreteTree`/`GenArena` file pair with K=2 data
(genArenaCNF for 24 bits, encode_complete already generic). Est. 1-2
sessions + a few CPU-hours. Optional: supersede later by the any-K theorem
(which covers K=2), keeping this as an independent double-check.

## 5. Risk register

| risk | exposure | mitigation |
|---|---|---|
| `Array.qsort` mem API missing | B8, C-data | P3 refactor to mergeSort + overnight recount |
| `mem_partitionsN` proof pain | B4 | labeling-enumerator fallback (rerun census count) |
| LRAT data > Lean budget | C3 | cake_lpr streaming (K=3-proven), external axiom |
| 1.4M coverage native_decide slow/matches nothing | C4 | precompute canonical forms; Route B fallback |
| transport lemma subtleties (axis negation on ℤ³) | C4 | K=3 PInvFinish as template; validate the finite core by native_decide first |
| digit-extraction lemma fiddle | B5 | fixed-base bespoke induction, only j ≤ 5 needed — could even case-split |
| big numeral grids slow elaboration | C2 data | split into per-cert defs; binary numerals are compact |

## 6. Suggested session plan

1. **S1 (Python + small Lean):** P1-P3 pre-flights; dedupSorted refactor +
   census_count rerun overnight; B1-B2.
2. **S2:** B3, B5, B6 (+ B4 attempt; fallback decision by end of session).
3. **S3:** B7 (+ finish B4/B8) → `census_complete` compiles.
4. **S4:** C1-C2 (+ generate empty certs overnight; P2 decision executes).
5. **S5:** C3.
6. **S6:** C4 transport + coverage.
7. **S7:** M5 assembly + axiom audit + writeups. Optionally anyk-03 in
   parallel any time.

Terminal state: `#print axioms no_aperiodic_wang_cube_anyK` =
[propext, Classical.choice, Quot.sound, Lean.ofReduceBool,
Lean.trustCompiler] (+ `frontierEmptyFacts` only if the cake_lpr route is
forced — aspire to none).
