---
title: "Constructive route — try to embed a known aperiodic 3D Wang-cube set into one orbit"
status: done
claimed_by:
created: 2026-07-16T17:27:36Z
updated: 2026-07-16T17:27:36Z
---

## Description

The direct attack: if a known aperiodic Wang-cube set embeds in a single
rotation orbit at some finite K, the einstein exists and the whole any-K
question resolves constructively.

1. Literature pass first (WebSearch/WebFetch): pin down the best known
   aperiodic 3D Wang-cube sets — Culik–Kari 1995 (~21 cubes, Kari's
   arithmetic/Beatty-sequence method) and anything smaller or more
   structured since; extract exact tile counts + matching relations into
   machine-readable form. Also collect how their aperiodicity proofs work
   (we'll need to transport the proof through the embedding, not just the
   tiles — anyk-13).
2. Run `orbit_embed` (anyk-08) against each target at increasing K. The
   target has ≤24 tiles as a hard requirement — if the smallest known sets
   exceed what one orbit can host under the simulation notion, look for
   set-shrinking preprocessing (tile fusion / product constructions) before
   giving up.
3. Mine the failures: if UNSAT at every tried K, extract *why* (unsat cores
   over the slot-algebra constraints) — a K-independent failure pattern here
   is exactly the raw material anyk-12 needs for the obstruction.

**Done when:** either (a) an embedding is found — deliver the decoration,
its K, and a verified round-trip of the simulation (then escalate to
anyk-13: aperiodicity transport), or (b) a documented negative across the
tried targets/K-range with extracted failure structure, handed to anyk-12.

**Blocked by:** anyk-08 (needs orbit_embed and the simulation definition).

## Progress

- (2026-07-19) **Superseded by the census result** (anyk-08: every
  achievable relation at every K is empty or periodic — zero aperiodic).
  No embedding of an aperiodic set into a single rotation orbit can exist
  in this family: the orbit's relation would be an achievable aperiodic
  relation, and there are none. The still-useful residue of this card is
  the **literature pass** (Culik–Kari exact tile data, prior 3D
  aperiodicity constructions) — reassigned to the paper plan
  (PLAN-papers.md §related-work). Status: retired as a construction task.
