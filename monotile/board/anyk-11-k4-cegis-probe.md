---
title: "Instrument — exploratory K=4 arena run (does the screw taxonomy persist at 96 bits?)"
status: done
claimed_by:
created: 2026-07-16T17:27:36Z
updated: 2026-07-16T17:27:36Z
---

## Description

Timeboxed instrument, not a closure attempt. Launch `ARENA_K=4 ./run.sh`
(96-bit decorations; CEGIS proposal SAT instances are fine at 96 vars — the
open question is verifier cost and loop convergence) and watch three things:

1. Kill taxonomy: is every periodic kill still a screw (run the
   `SCREW_STRUCTURE`-style decode on the K=4 pattern library as it grows)?
   Screws-only at K=4 supports the obstruction route; the first non-screw
   periodic structure is a genuinely new object — capture it.
2. Library growth: does the forbidden-pattern library trend toward
   saturation (K=3: 33 patterns, sharp) or keep growing (signal of richer
   structure the small-K certificate style won't capture)?
3. Survivors: anything reaching suspicious/deep-survivor goes straight to
   the deep_check gauntlet.

Engineering notes: check the K-dependent constants flow through `ARENA_K`
everywhere (orbit tables, balance CardEnc, canonical period-vector orbits);
expect per-iteration cost well above K=3 — set conflict budgets accordingly
and keep the lazy pattern-library discipline. Checkpoint from the start
(the saturate2-style done-file pattern) since any long run must survive
session death.

**Done when:** the timebox (suggest: a few days of background compute)
yields a written read on 1–3 above, with the pattern library persisted for
whoever comes next. Explicitly not done-when-closed — closure at K=4 is not
this card.

**Blocked by:** nothing. Cheap to start, informative even when partial.

## Progress

- (2026-07-19) **Superseded by the census result** — the questions this
  instrument was built to answer (does the screw taxonomy persist? does
  the library saturate?) are answered at the relation level for all K at
  once: 9,363 periodic relations, max index 64, all "screws" in the
  generalized sense; nothing aperiodic. A K=4 arena run would be
  redundant confirmation. Retired.
