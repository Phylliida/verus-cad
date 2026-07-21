---
title: "K=3 mining — classify the 3 undetermined patterns (complete the irredundancy census)"
status: in_progress
claimed_by: fable
created: 2026-07-16T17:27:36Z
updated: 2026-07-16T18:00:00Z
---

## Description

The one-pass MUS run over the 33 forbidden patterns left 3 undetermined:
dropping each leaves a 4³ instance that neither fast-SATs nor fast-UNSATs at
200s (the other 30 are individually load-bearing — removal resurrects a
counterexample tiler in 0.2–30s; none is redundant). Identify which 3 from
the mining logs, then resolve each drop-instance with the lex +
cube-and-conquer treatment (same as anyk-04).

Why bother: "the certificate is irredundant — exactly N/33 patterns
load-bearing" is a clean, paper-grade statement about the obstruction having
no shorter form, and it's currently fuzzy at N ∈ {30..33}.

**Done when:** each of the 3 is classified load-bearing (drop → SAT witness
found) or redundant (drop → still UNSAT, cert verified), and the census
number is exact. If any turn out redundant, note whether the reduced set
still yields all-screw structure (it will — subset — but say so).

**Blocked by:** nothing. Compute-bound, background-friendly. Shares tooling
with anyk-04.

## Progress

- (2026-07-16T18:00Z) Rather than dig for the original mining logs, re-ran
  the whole census with the tractability trick the closure run validated:
  `mine_drop33.py` builds all 33 drop-one instances at 4³ with **full-48
  lex** (sound at the cubic box: pattern set rotation-closed by
  construction, e-var blocks flip-invariant) — the original MUS pass ran
  without lex. 33 × ~666K clauses in `drop_census/`.
- (2026-07-16T18:02Z) Solving: 6 parallel cadical workers, 900s cap each
  (`drop_census/results.log`, exit 10=SAT/load-bearing, 20=UNSAT/redundant,
  0=timeout/undetermined). Expected: ~30 fast SAT; the stragglers are the
  interesting ones.
- (2026-07-16T18:35Z) First pass done: **30/33 SAT (load-bearing), and the 3
  timeouts are drops 14, 17, 18** — an independent reproduction of the
  original census's "3 undetermined" (which it never named; now they're
  identified). Relaunched those three uncapped
  (`drop_census/results_long.log`); if they run overnight without resolving,
  next step is cube-and-conquer per instance.

- (2026-07-19) Uncapped runs 3+ days in, unresolved. Endgame plan: kill and
  cube-and-conquer each drop-instance (cube_k2.py pattern on drop_NN.cnf,
  split on the 54 decoration vars). Low priority — paper-polish only; the
  any-K census supersedes the significance. Park or cube at next session's
  discretion.
