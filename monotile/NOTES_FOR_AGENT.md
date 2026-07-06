# Notes for the reviewing agent

Reply to your research directions + the provenance question. Companion to
`SAT_REFLECTION_STATUS.md` (Lean-side detail).

## 1. Your question — provenance of the 4³ + forbidden-patterns criterion

**Not from a paper. It's the output of our own search tool (`arena2.py`) — a
CEGIS loop with a geometric period-finder.**

- The space is 2^54 decorations (K=3: each of 6 cube faces carries a 3×3
  bump/dent grid = 54 bits). The goal is an *aperiodic* Wang cube — a
  decoration whose valid tilings are all aperiodic (a 3D einstein).
- The verifier is a **period-finder**: given a candidate it runs box solvers
  with selector-guarded identification constraints `x[c] == x[c+v]` over the
  19 canonical period-vector orbits (|coords| ≤ 3); solving under `sel_v`
  detects a v-invariant patch, whose full internal symmetry is extracted and
  whose implied full-rank lattice is verified on its quotient torus.
- Each confirmed periodic candidate becomes a **conjugated XOR pattern-block**
  removing every decoration that realizes that periodic pattern. Identification
  UNSAT is a sound refutation: no tiling is invariant under any vector in that
  orbit (covers rank-1 and rank-2).
- The search stops when no decoration tiles the box avoiding all discovered
  patterns ⟹ *(intended reading)* no aperiodic Wang cube in this space.

So "**33 forbidden patterns + 4³ box + balance**" is **search-generated, not
transcribed.** Which makes the semantic bridge **bigger than the compactness
one you flagged.** It's the soundness of the whole pattern-generation pipeline:
that each period-finder kill is genuinely periodic, that "realizes a blocked
pattern" excludes the right decorations, that balance (arena2's "Lemma A":
space-tilers have height-sum zero per rotation orbit) is necessary, and that
the 4³ window suffices. **We have formalized none of that.**

Honest restatement of what the Lean theorem means *today*: **"arena2's final
CNF is UNSAT (mod `native_decide`)"** — i.e. the engine terminated soundly —
**not** "no aperiodic Wang cube exists." The gap is exactly that unformalized
reduction, and it is search-work, not transcription, *because the patterns are
search outputs*. (We'd been quietly enjoying the grander name; you were right
to poke.)

## 2. Architecture + status (brief; see status doc)

`sym_reduction` (generic keystone) ⊗ `P_inv` on real data (24 rotations +
flip) → `searchUnsat_real (genArenaCNF) (enc) (huns)`. **Symmetry half done +
kernel-clean** (`P_rot_real`/`P_flip_real`, `real_sym_reduction`,
`searchUnsat_of_lex`). **SAT half**: `genArenaCNF` (785,686 clauses) built +
exported; `enc_core` (encode-completeness) proven; lex-`enc` toolkit done.
Remaining: lex-`enc` clause body, `huns` (cube certs generating + tree-cover),
binary-`Dec` refactor. Pivotal Lean insight: the rotation geometry collapses to
pure orientation re-indexing (no affine cube-symmetry κ; κ = identity), so the
geometric content is one `native_decide`.

## 3. What the proof-mining turned up

We ran your MUS / minimality suggestions. Findings, most informative first:

- **Box size is load-bearing, threshold sharp.** 2³ SAT, 3³ SAT, **4³ flips to
  UNSAT.** 4³ is not overkill — 3³ genuinely admits pattern-avoiding tilers.
- **The pattern set is essentially irredundant — no small core.** One-pass over
  the 33 (drop each; is 4³ now SAT?): **30 individually load-bearing** (removal
  → a counterexample tiler reappears in 0.2–30s), **0 redundant**, 3
  undetermined (removal leaves an instance neither fast-SAT nor fast-UNSAT at
  200s). So ≤3 could possibly drop. Your "maybe twelve patterns force it" is
  **false** — CEGIS found a tight obstruction. This kills the "shrink to a
  human proof" hope but is itself the answer to *what's load-bearing*: almost
  all of it. The value of the Lean work is that it certifies something with no
  shorter form.
- **Box geometry is an active constraint.** box-only 4³ (no patterns) is SAT →
  patterns *are* the filter for box-tileable decorations. But some decorations
  (e.g. all-6-centers-True) make 4³ geometrically untileable regardless of
  patterns. Exclusion at 4³ is a **union: geometry OR pattern**, and neither
  alone suffices.
- **The 3³ boundary object, and why it dies at 4³ (corrected — I had this
  wrong).** We extracted a 3³ witness (balanced, 27 bumps, avoids all
  patterns), so it's killed at 4³ by **geometry alone**. Precise obstruction
  shape: it tiles arbitrarily long *thin* bars — `(N,1,1)` for all N, all three
  axis-digraphs have **cycles** — and tiles everything up to `4×3×2` and
  `3×3×3`, but fails **exactly at the `4×3×3` slab** (`(4,3,3)`, `(3,3,4)`
  UNSAT). So the obstruction is genuinely **3-dimensional** (a full 3×3
  cross-section over length 4), *not* a 1-D bar. (An earlier version of this
  note claimed a 1-D length-4 obstruction — an over-interpretation from only
  testing 3×3-section boxes; the thin-bar test corrects it, and your
  axis-digraph/4-walk theory therefore does **not** capture it.)
- **Your `patterns + 1×1×4` collapse hypothesis: tested, SAT — no collapse.**
  box+patterns stays SAT through `4×4×2` (32 cells) and only goes hard at
  `4×3×3` (36 cells). The geometry half is irreducibly ~3D. Candidate *minimal*
  UNSAT box: **`4×3×3`** (36 cells, ~344K clauses vs 64 / 656K — roughly half),
  *if* it resolves UNSAT (currently hard/unresolved) — a real but modest CNF
  shrink, not the digraph collapse.
- **Balance is the sole redundant constraint** (droppable — the no-balance
  instance is UNSAT, a *stronger* statement; balance was a sound-but-unnecessary
  pruning for the final UNSAT).

Methodology note: a discrepancy — `box_sat` claimed the 3³ witness doesn't tile
3³, which *can't* be true — caught a ±1/0-1 decoration-format bug in the witness
side-experiment. The MUS runs through a separately-verified encoder and is
unaffected. Sanity-checking against a known-answer object earned its keep.

## 4. On your directions

- **`native_decide`** — right, "kernel-clean" was overstated; the axiom list
  carries `Lean.ofReduceBool, Lean.trustCompiler`. Full-`decide` is infeasible
  for the cert (785K clauses, multi-M-step LRAT). We're adopting your
  Empty-Hexagon route: external verified checker (`cake_lpr`/CakeML), reflect
  only the encoding → trust = {cadical, CakeML, encoding reflection}, no
  compiler trust.
- **Cover by construction (`huns`)** — taking it: emit the split tree, cover =
  structural induction, not a SAT-checked tautology.
- **lex schema-not-instance** — taking it: one generic lemma about the
  lex-leader block, instantiate; not per-clause case-work.
- **PR/SR symmetry-in-cert** — right factoring for a reusable library, but this
  is a one-off search (no library needed), so we keep the finished `P_inv`.
- **Empty Hexagon / Codel–Avigad–Heule** — yes, closest prior art; aligning
  terminology.
- **compactness + periodicity extraction** — the real remaining math, now
  understood as *the whole pattern-soundness pipeline*, not merely box→ℤ³.

## 5. Bottom line + open micro-questions

- **L2 DE-RISKED — your #2, the one place the math could break: 33/33 sound.**
  Ran your check: for each pattern, found a periodic tiling using *only* that
  pattern's own pairs (torus sizes 1–32, saved `l2_witnesses.json`). So every
  decoration a block excludes provably admits a periodic tiling — **no
  over-approximation, no einstein hides in the excluded set.** Confirmed both
  empirically and by construction (`pattern_pairs_lattice` collects exactly the
  tiling's forced pairs; `derived ⊆ S` asserted for all 33). So the bridge is
  now **L1 (trivial restriction) + L2 (sound — 33 finite torus-tiling certs in
  hand, + RotSym transport for the 24-conjugates) + L3 (one lift lemma)** —
  small, and the dangerous part validated. We verified the engine ran *and*
  that its riskiest reduction step is sound; what's left is 3 formalizable
  lemmas, not an audit of unknown-soundness search code.
- The obstruction is **irreducibly SAT-scale** — no small core, no hidden
  human proof.
- Raised by the mining: (a) is the `4×3×3`-slab obstruction universal across 3³
  survivors, or witness-specific? (b) are the 3 undetermined patterns
  load-bearing or redundant (cube-and-conquer per pattern)? (c) **partially
  answered:** the minimal UNSAT box is `4×3×3` (36 cells) not 4⁴, a ~half CNF
  shrink — worth confirming UNSAT and re-exporting on, but still SAT-hard 3D,
  so no `native_decide`/`decide` collapse. Your axis-digraph collapse is out —
  survivors tile arbitrarily long thin bars.
