---
title: "Constructive route — revive the frame-lock / Robinson co-design at K≥4 payload budgets"
status: done
claimed_by:
created: 2026-07-16T17:27:36Z
updated: 2026-07-16T17:27:36Z
---

## Description

The second constructive attack, resuming the parallel session's program from
where its no-go theorems stopped. Recap: the frame-lock architecture splits
the decoration into a *lock* (bits that rigidify which orientations can meet,
e.g. the axis-coset lock H=stab(z), |H|=8, validated SAT at K=3 in
`rigidity.py`) + a *payload* (remaining bits, on which one builds a
hierarchical aperiodic system — the "dual transverse Robinson systems"
design). The parallel session closed this at K=3-era alphabets: no-go for
8-letter D4 and 12-letter A4 lock+payload co-design (arena3/arena4), with the
thesis "8 and 12 letters are below the 3D aperiodicity threshold."

K=4 changes the budget: 96 bits total, so after any lock there is far more
payload than the 30 bits the K=3 design had to squeeze into. The K=3 no-gos
say nothing about this regime.

Steps:
1. Recover the tooling: `rigidity.py` is local; `arena3.py`,
   `theory_forensics.py`, `forensics_log.json` were parallel-session outputs
   we never received (`arena4.py`/`arena4_forensics.py` are local, archived).
   Rebuild what's missing rather than blocking on archaeology — the memory
   note + `letter_to_parallel_claude.md` document the design.
2. Re-derive the lock menu at K=4 (which orientation-subgroup locks are
   SAT + verified at 96 bits; the K=3 result: full lock UNSAT, axis-coset
   lock SAT for both channels).
3. Co-design search: lock + Robinson-style payload over the enlarged
   alphabet. This is a structured synthesizer (CEGIS over the design space,
   like arena4) — not a blind sweep.

**Done when:** either (a) a lock+payload candidate that defeats the
period-finder at depth (→ deep_check gauntlet → einstein candidate →
anyk-13), or (b) a no-go for a well-defined K=4 design space, stated
precisely enough to be a data point ("N-letter transverse systems below
threshold" extended), or (c) an honest "design space too big to close,
here's the frontier" writeup.

**Blocked by:** nothing. Independent of anyk-08/09; the two constructive
routes can race.

## Progress

- (2026-07-19) **Superseded by the census result**: a successful
  lock+payload co-design at any K would realize an achievable aperiodic
  relation; the census proves none exists. The frame-lock program's no-go
  intuition ("8/12 letters below threshold") is now a theorem-shaped fact
  for ALL letter budgets in this family. Retired; the design-history
  belongs in the paper's narrative.
