---
title: "Obstruction route — the equivariant orientation-SFT reformulation + the K-free question"
status: in_progress
claimed_by: fable
created: 2026-07-16T17:27:36Z
updated: 2026-07-16T19:50:00Z
---

## Description

Make the screw reading into K-independent mathematics. The key observation
to develop (and check carefully — the stabilizer caveat below can dent it):

For a fixed decoration d with free orbit, a tiling of orbit(d) *is* exactly
an orientation field ω : ℤ³ → Rot24 subject to nearest-neighbor constraints:
cell c holds tile ω(c)·d, and validity is Compat(ax, ω(c), ω(c+ax)) for the
axis-wise compatibility relation induced by d's face bits. The tiling is
fully determined by ω. So:

> Single-orbit aperiodicity at parameter K ⟺ some achievable Compat relation
> makes the 24-letter nearest-neighbor SFT on ℤ³ nonempty and aperiodic.

Two structural constraints make this special (and possibly impossible):
- Equivariance: Compat is not arbitrary — it is induced by one decoration,
  hence invariant under the simultaneous rotation action (relating
  Compat(ax, o1, o2) across rotated axes/orientations; the exact form is the
  `pairs_equiv` fact already native_decide'd at K=3 in `PInvFinish.lean`).
- Achievability: which equivariant relations are realized by some d at some
  K (this is anyk-08's slot algebra; as K→∞ conjecture the achievable set
  saturates everything equivariance + complementarity parity allows — prove
  or refute).

That splits the any-K question cleanly:
(A) Is every "legal" equivariant relation achievable at large K? (finite
    combinatorics per relation — 24 letters, 3 axes, so finitely many
    relations total; possibly fully decidable by orbit_embed sweeps.)
(B) Does any nonempty aperiodic equivariant 24-letter NN SFT on ℤ³ exist?
    (K has vanished. This is now a question about one finite group.)

If (B) is no — the all-K no-go, and the K=3 machine result becomes one
instance of a theorem about finite orientation groups. If (A) and (B) are
both yes — the einstein exists, constructively via anyk-08/09.

Sub-tasks: write the reduction note precisely, incl. the non-free-stabilizer
regime (decorations with rotational self-symmetry give quotient alphabets —
either handle or show WLOG-free); connect to the K=3 evidence (all 33 kills
are screws = at K=3, every nonempty achievable SFT has a screw-periodic
point); formulate the finite candidate statement "every nonempty equivariant
NN SFT on Rot24 has a periodic point" and hunt for either a proof strategy
(the finitely-many-relations observation means brute enumeration of
relations + per-relation SFT analysis is at least *statable* as a finite
computation — estimate its size honestly) or a counterexample relation
(which then needs achievability, route (A)).

**Done when:** the reduction note exists with the ⟺ proved at the
appropriate rigor (paper-level; Lean later if it becomes the theorem), the
(A)/(B) split is stated exactly, and there is a concrete assessment of
whether (B) is finitely checkable and at what cost. This card is thinking +
writing, not compute.

**Blocked by:** nothing. Dual to anyk-08; the failure mining from anyk-09
feeds it.

## Progress

- (2026-07-16T19:50Z) Prompted by Danielle's question ("can Lean prove,
  assuming SAT results, that no K is possible?"): wrote
  **`DESIGN-anyk-lean.md` v0.1** — the full conditional-formalization
  architecture. Key upgrades over this card's original sketch: (i) the
  achievability question reduces to face-equation gain-graph consistency
  over D4×Z2 with a K-parity fixed-point analysis, plausibly with a concrete
  K₀ bound making enumAchievable a native_decide computation; (ii) the
  per-relation SAT instances are tiny (24-letter SFT boxes, ~5k vars — no
  decoration/e-vars/balance), small enough for the in-Lean verified checker,
  so the all-K theorem could land on kernel + native_decide only, a
  *stronger* trust base than K=3's; (iii) fail-forward: a stalled relation
  + achievability = an einstein candidate construction. Dress-rehearsal plan:
  build the whole pipeline in 2D first (C4, 4-letter SFTs) and cross-check
  against arena2d's exhaustive sweeps.
- (2026-07-16T20:40Z) **Dress rehearsal Python half COMPLETE, same day**
  (`RESULTS-2d-anyk.md`): the (B)-question is answered in 2D — every
  achievable equivariant relation (116 of them, exactly characterized) has
  an empty or periodic SFT, periods at C4's element orders. So *no 2D
  single-orbit einstein at any K*, empirically, with every chain link
  machine-validated. What remains here: the Lean port (checklist in the
  RESULTS doc) and then the 3D lift, where question (B) is genuinely open.
- (2026-07-16T23:30Z) **LEAN PORT COMPILED + AXIOM-AUDITED, same day.**
  `AnyK2D.no_aperiodic_wang_square` on [propext, Classical.choice,
  ofReduceBool, trustCompiler, Quot.sound] — kernel + native_decide only.
  Key architecture wins recorded in RESULTS-2d-anyk.md. This card's 2D
  scope is DONE; the remaining scope is the 3D lift (with anyk-08's 3D
  slot algebra as the next concrete step).
