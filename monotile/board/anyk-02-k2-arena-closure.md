---
title: "K=2 — run the arena to closure (pattern saturation + final box UNSAT with verified certs)"
status: in_progress
claimed_by: fable
created: 2026-07-16T17:27:36Z
updated: 2026-07-16T19:35:00Z
---

## Description

Close K=2 the way K=3 was closed. K=2 is 24 bits (2²⁴ decorations), not
implied by the K=3 theorem (lifting goes upward: K=2 ⊂ K=4, not K=3), and the
2026-07-06 run was already at 79 iters / 73 periodic kills / 0 survivors when
it budgeted out. Closing it upgrades the headline to "no aperiodic binary
Wang cube for any K ≤ 3" and is a full second exercise of the pipeline.

Steps:

1. Relaunch `ARENA_K=2 ./run.sh <budget>` (checkpointed pattern library in
   `arena2_patterns_K2.json`, warm-start kills are cached) until the CEGIS
   loop stalls with an exhausted proposal space, i.e. box + patterns + lex +
   balance UNSAT.
2. Find the closing box. K=3 closed at 4³ with a sharp 3³/4³ threshold —
   measure the K=2 threshold (try 3³, 4×3×3, 4³). Smaller box = smaller CNF
   downstream.
3. Final UNSAT with certificates: adapt the K=3 cert pipeline
   (`gen_cube_certs.py` → cadical `--lrat` → cake_lpr via `run_sat.sh` /
   `stream_verify.py`, cover tree via `export_tree.py`). Lex symmetry-breaking
   was the tractability key at K=3 (`add_lex_leaders`); expect the same here.
   At 24 bits this should be far cheaper than the K=3 grind.

**Done when:** either (a) every cube cert verified + cover complete — K=2
search-closed, hand off to anyk-03 for the Lean port — or (b) a
deep-survivor emerges (einstein at K=2 — would be shocking given 73/73 kills
so far, but report it, don't argue with it).

**Blocked by:** anyk-01 (the parked suspicious decorations must be classified
first — a deep-survivor invalidates this card's premise).

## Progress

- (2026-07-16T19:35Z) anyk-01 closed with zero survivors (all 8 parked
  decorations were non-tilers) — premise intact, no library additions
  needed. Warm-start closure run launched: `ARENA_K=2 ./run.sh 14400`
  (`arena2_k2_closure.log`), resuming from the checkpointed pattern library
  (~73 periodic kills so far). Watching for STALL/closure vs. new
  suspicious.
- (2026-07-16T21:30Z) Run ended `SYNTH_BUDGET` at iter 72: library replay
  (71 cached kills) + 1 new untileable8, then the synthesizer could neither
  propose nor refute within the escalating conflict budget — the endgame
  signal. Next: static CNF (4^3 box + library + full-48 lex, cubic box so
  full lex is sound) + cube-and-conquer, the K=3 closure recipe.
  cube_conquer3.py is K-generic via ARENA_K but its artifact paths
  (grind3*.log/jsonl, arena2_patterns.json backfeed) would collide with the
  K=3 closure artifacts — needs a paths pass before launching.
- (2026-07-17T00:00Z) Endgame launched the simpler way first:
  `mine_k2_static.py` reuses cube_conquer3.build_cnf verbatim under
  ARENA_K=2 → `k2_static.cnf` (3,228 vars / 322,284 clauses / 77 patterns,
  full-48 lex baked in). Solving with **LRAT cert generation from the
  start** (`cadical --lrat`, `k2_static_solve.log`) per Danielle's
  requirement that K=2 lands formally checked like K=3: UNSAT cert →
  cake_lpr → Lean (anyk-03). Note the closure statement includes the
  point-blocks, so anyk-03 also needs the 8 point-refutation certs
  (untileable5/8) alongside pattern certs. If the monolithic lexed solve
  stalls, fall back to cube-and-conquer with per-cube certs (K=3 recipe).
