---
title: "Endgame — reconcile the routes into an any-K answer"
status: in_progress
claimed_by: fable
created: 2026-07-16T17:27:36Z
updated: 2026-07-16T17:27:36Z
---

## Description

The goal card, kept explicit so the program doesn't mistake sub-results for
the destination. Branches, depending on what 06–12 return:

- Candidate found (2D via anyk-07, or 3D via anyk-09/10/11): a candidate is
  not a result. It must survive the deep_check gauntlet, and then
  aperiodicity must be *proved* — the period-finder failing to kill it is
  evidence, not proof. Expected proof shape: transport the source set's
  aperiodicity argument (hierarchy / Kari arithmetic) through the embedding
  or design; then decide how much to formalize (the K=3 Lean stack gives a
  head start on the periodic-side machinery, but an aperiodicity proof is
  new territory — hierarchical structure arguments, not SAT).
- Obstruction proven (anyk-12 route B is no): assemble the all-K theorem —
  achievability analysis (A) + the equivariant-SFT periodic-point theorem
  (B) + the orbit reformulation ⟹ no aperiodic Wang cube at any K.
  Formalization plan: the reformulation and (A) are finite/data-heavy (the
  K=3 pipeline's style transfers); (B) is the real theorem.
- Neither within reach: write the frontier honestly — the K≤3 closures
  (01–05), the 2D phase diagram (07), the orbit structure theory (08), and
  the exact open statement (12's (B)) are a coherent publishable program
  snapshot even without the final answer.

**Done when:** one of the branches lands with the standard of rigor this
project has held so far (machine-checked or explicitly marked otherwise),
and the board gets its closing anchor entry.

**Blocked by:** everything. That's the point.

## Progress

- (2026-07-19) **The branch is chosen: obstruction proven (empirically),
  einstein ruled out for this family.** The census classified every
  achievable relation at every K: empty or periodic, nothing aperiodic —
  in 2D (kernel-checked theorem) and 3D (all computations done,
  formalization = anyk-14 / DESIGN-anyk3d-endgame.md). This card's
  remaining scope = the formal assembly landing (M5) + the honest write-up
  (PLAN-papers.md). The "einstein found" branch is closed; the "neither
  within reach" branch is moot.
