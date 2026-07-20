# S1 pre-flight results (P1/P2/P3) — 2026-07-20

Raw outputs of the three pre-flight jobs from DESIGN-anyk3d-endgame.md §0,
recorded durably (job scratch files are ephemeral). Feeds the M4 route
decision.

## P1 — raw-frontier sizes (`p1_rawfrontier.log`)

    raw candidates (orbit of canonical frontier): empty 75,054 / periodic 5,150
    raw maximal-empty antichain:   26,452   [83s]
    raw minimal-periodic antichain:   870   [85s]
    raw profiles:              1,445,865
    sample coverage (10k random raw profiles): 10000/10000 covered  [121s]

Artifact: `anyk3d_frontier_raw.json` = {rawMaxEmpty[26452], rawMinPeriodic[870]}.

**Reading.** Route B's raw antichains are 26,452 + 870 — the empty side is
~7.8× the canonical 3,405, well above the "≲15k → Route B tempting"
threshold. Coverage of raw profiles by the raw frontier is total on the
sample (expected — it is by construction the frontier of the classified
set, closed under the orbit). This measures antichain SIZE, not cert cost;
cert cost is P2, and P2 is what actually decides.

## P2 — empty-cert sizing (`p2_sample/`, sampler in-line)

Frontier verdict mix (the 3,405 canonical maximal-empty by box-tier):

    empty3: 3,371   empty4: 18   empty5: 13   empty6: 3

Sample LRAT sizes (cadical --lrat at each mask's classified box):

    empty3:  n=24  avg=107 KB     max=478 KB       (box 3^3)
    empty4:  n=4   avg=22.3 MB     max=86.8 MB      (box 4^3)
    empty5:  n=4   avg=73.6 MB     max=292 MB       (box 5^3)
    empty6:  n=3   avg=3.16 GB     max=9.48 GB      (box 6^3)
    projected total for all 3,405: ~11.5 GB   [5484s]

**Reading — this is the load-bearing result of S1.** The frontier is
radically bimodal. The 3,371 empty3 masks are trivially cheap (~107 KB;
all 3,371 ≈ 360 MB total, in-Lean `verifyCert`-able if chunked). The
34 stragglers (empty4/5/6) dominate everything: the three empty6 certs
alone project to ~9.5 GB, and a single box-6 LRAT (9.48 GB) will not fit
in a Lean source file nor check comfortably even via cake_lpr streaming.

Consequence for M4-C3: neither pure route (all-in-Lean, or one uniform
cake_lpr axiom) is right. The straggler boxes need a smaller certificate,
not a bigger pipeline. Options to weigh next session (NOT yet decided —
this is a Danielle-facing design fork):
  1. **Shrink the box.** empty5/empty6 verdicts used 5^3/6^3 because the
     classifier's tiers stopped there; a *non-cubic* or MUS-minimized
     window may certify the same emptiness in far fewer clauses (cf.
     anyk-04: 4x3x3 beat 4^3). Re-mine minimal boxes for the 34 only.
  2. **Cube-and-conquer the 34.** Split each straggler into cubes with
     small per-leaf certs (the K=3 / K=2 recipe), stream via cake_lpr.
  3. **Deeper frontier compression.** Some of the 34 may be dominated by
     *combinations* below the maximal antichain — check whether a
     non-antichain cover with cheaper witnesses exists.
Recommended first move: option 1 on the 34 (cheap Python mine), re-measure,
then choose. The 3,371 cheap ones proceed to in-Lean verifyCert regardless.

## P3 — dedupSorted refactor + recount

- Core API confirmed: `List.mergeSort` has `mem_mergeSort`, `mergeSort_perm`,
  and a `@[csimp]` tail-recursive impl (`Init/Data/List/Sort/`). `Array.qsort`
  has no membership lemmas — refactor was necessary.
- `dedupSorted` refactored to `(a.toList.mergeSort (· ≤ ·)).foldl …`.
- Recount PASSED (`bxl2blzrk.output`: "RECOUNT+OLEAN OK"):
  `census_count_fast : censusFast.size = 1445865` re-verified on the
  refactored code; olean rebuilt/banked.
- Axioms unchanged: [propext, Classical.choice, Lean.ofReduceBool,
  Lean.trustCompiler, Quot.sound] — kernel + native_decide, no regressions.

## Net decision state going into S2

- **Route A stands** (canonical frontier + rotation transport). P1 confirms
  Route B's antichains are too large; P2's straggler blowup would hit Route
  B even harder (more masks × the same fat-tail boxes).
- **M4-C3 empty side is now a two-tier plan**: 3,371 cheap → in-Lean
  verifyCert (chunked); 34 stragglers → resolve via smaller certificates
  (mine minimal boxes first). This refines DESIGN §C3's "P2 decides
  verifyCert vs cake_lpr" into "verifyCert for the body, special-case the
  fat tail" — worth a design-doc amendment + a Danielle check before the
  cert campaign.
- **B1-B3 + B6 landed** in `AnyK3DBridge.lean` (B6 compile pending at the
  session pause). Recount unblocks building M3b membership on the refactored
  `dedupSorted`.
