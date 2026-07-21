---
title: "K=2 — triage the 3 parked suspicious decorations through the deep_check gauntlet"
status: done
claimed_by: fable
created: 2026-07-16T17:27:36Z
updated: 2026-07-16T19:30:00Z
---

## Description

The K=2 arena run (2026-07-06, `ARENA_K=2`) ended at BUDGET with 3 decorations
parked in `arena2_log_K2.json`'s suspicious list:

1. One genuinely unresolved: budget-outs on 11 identification boxes
   (`det4`/`det6` at various vectors) + `box5` — i.e. neither periodic nor
   refuted. `[1,1,-1,-1,-1,-1,1,1,-1,-1,1,1,-1,1,-1,1,1,-1,1,-1,1,1,-1,-1]`
2. Two marked `untileable8` (failed to tile the 8-box) but sitting in the
   suspicious list rather than confirmed dead.

Re-judge each through the full K=3-era gauntlet, adapted to K=2:
`lattice_sweep` (all 1,634 lattice classes ≤32 via `skew.lattice_classes`)
+ `deep_check` (sweep + EXTRA4 coordinate-4 vectors at 6³ and 8³ boxes).
Remember the engine lessons: budget-out = "unresolved", never refutation;
never trust a single patch to show symmetry; escalate conflict budgets rather
than concluding.

Check first whether `deep_confirm.py` / `deep_check` respect `ARENA_K` — they
were exercised at K=3; the K-dependent constants (54 bits, orbit tables) come
from `arena2.py` module state, so importing under `ARENA_K=2` should work, but
verify on a known-periodic K=2 kill before trusting verdicts.

**Done when:** each of the 3 is classified as exactly one of:
- periodic (index recorded, pattern added to `arena2_patterns_K2.json`),
- untileable (confirmed non-tiler, dead),
- deep-survivor (tiles deep boxes, no lattice ≤32 — escalate immediately; this
  would be an einstein candidate and blocks anyk-02 pending resolution).

**Blocked by:** nothing. Cheap; do first.

## Progress

- (2026-07-16T17:40Z) Reconstructed the parked set from the full
  `arena2_progress_K2.jsonl` (156 records, two runs — the final json is stale
  w.r.t. the second run): it's **4 distinct suspicious decorations** (iters
  57, 58, 61, 77) + **4 untileable8** (not 1+2 as the description said).
- (2026-07-16T17:40Z) Audited the untileable8 semantics: `box_solver_cnf` is
  free-boundary (internal matchings only), so `box_sat(8³) == False` is true
  UNSAT and soundly refutes space-tiling. The 4 untileable8s are already
  confirmed dead; only the 4 suspicious need the gauntlet. One untileable8
  re-run included as an audit spot-check.
- (2026-07-16T17:45Z) `triage_k2.py` running (log: `triage_k2.log`, results:
  `triage_k2_results.jsonl`; generic runner `runpy.sh` added). Pipeline
  validation passed: fresh random K=2 periodic kill (index 4) confirmed
  `periodic-deep` by deep_check in 10.4s — K=2 verdicts trustworthy.
- (2026-07-16T17:50Z) Suspicious #0 (the it58 one): `ext-timeout` after 137s
  — nothing ≤32 in the lattice sweep, then a 6³ identification solve hit the
  300k-conflict budget. Unresolved; will escalate budgets after the other
  three report.
- (2026-07-16T18:07Z) Suspicious #1 (it57): `untileable8` in 388s — true
  UNSAT at the free-boundary 8³ box, so it never tiled space at all. Sound
  kill. Two suspicious remain (#2, #3), then the audit spot-check.
- (2026-07-16T18:15Z) Suspicious #2 (it61) and #3 (it77): both `ext-timeout`
  (169s, 329s) — same profile as #0. Base-pass tally: 1 kill, 3 unresolved.
  Escalation pass staged (`triage_k2_escalate.py`: in-loop verdict at ~100×
  budgets, then lattice sweep to index 64 [10,076 classes, feasibility
  probed], 6³ at 3M conflicts, 8³ at 20M); launches when the base run's
  audit spot-check completes.
- (2026-07-16T18:40Z) Base pass complete; audit spot-check reproduced an
  untileable8 refutation in 1.7s. Escalation launched on the 3 ext-timeouts.
- (2026-07-16T19:20Z) Escalation verdicts: #0 (it58) **untileable5** (305s),
  #2 (it61) **untileable5** (264s) — both true-UNSAT at the 5³ box under
  escalated budgets, so neither ever tiled space; the base pass's det4
  budget-outs were just hard-instance noise. Tally: 3 of 4 killed, it77
  still in the gauntlet.
- (2026-07-16T19:30Z) #3 (it77) **untileable5** in 79s. All targets
  resolved; card done.

## Writeup

All 8 parked K=2 decorations are classified, and every one is a
**non-tiler** — none was periodic, none survived:

| decoration (run/iter) | verdict | how |
|---|---|---|
| 4 × untileable8 (both runs) | untileable (dead) | true UNSAT at free-boundary 8³ during the original runs; semantics audited (`box_solver_cnf` is free-boundary ⟹ sound refutation of space-tiling); one reproduced in 1.7s |
| it57 | untileable (dead) | base gauntlet, 8³ UNSAT, 388s |
| it58, it61, it77 | untileable (dead) | escalated in-loop verdict (~100× budgets): 5³ true UNSAT (305s / 264s / 79s) |

**Zero deep-survivors, zero new periodic patterns** — the K=2 pattern
library needs no additions from the parked set. The "suspicious" flags were
all hard-instance solver noise on non-tilers (their identification solves
budget out because the underlying box instances are near-UNSAT).

Method notes: pipeline validated first (random K=2 periodic kill →
`periodic-deep` in 10s); `runpy.sh` (generic env runner) added;
`triage_k2.py` + `triage_k2_escalate.py` are re-runnable; results in
`triage_k2_results.jsonl` / `triage_k2_escalate.jsonl`. Escalated gauntlet
tooling (index-64 sweep = 10,076 classes, 3M/20M-conflict boxes) is
reusable for anyk-02's endgame. Assumption on record: the two jsonl runs'
records fully cover the parked set (the stale `arena2_log_K2.json`
undercounted; reconstructed from `arena2_progress_K2.jsonl`).

**anyk-02 is unblocked** — no survivor invalidates its premise.
