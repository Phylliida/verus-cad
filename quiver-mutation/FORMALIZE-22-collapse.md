# Formalization request: the 22-sign-pattern collapse for `[C]`

We have a candidate endgame for proving `C=(-3,-2,-2,2,-2,2,-3,3,-2,-2)` is
mutation-abundant, reduced to a finite object. **We want your advice on how to
formalize the one remaining lemma** (§3), and whether the structure in §4 suggests a
clean proof or a better reformulation. Full context is in
`PROVE-C-mutation-abundant.md`; the essentials are below.

## 1. The reduction (proven)

`Goal (C mutation-abundant) ⟺ (R1) ⟺ [C] vortex-free ⟺ forkless part of [C] is
vortex-free.` [Unification: a bad window at `B` ⟺ `μ_k(B)` has a vortex on
`{m,o,k,l}`; forks are vortex-free (Burcroff), so all vortices live in the forkless
part.] Vortex-freeness is a pure **sign-pattern** (tournament) condition — no
magnitudes. So the infinite problem collapses to a statement about which tournaments
the forkless part realizes.

## 2. The collapse (verified)

The forkless part of `[C]` is infinite and grows **quadratically** in magnitude
(`~t²`), but realizes only **22 distinct sign-patterns** (tournaments on 5 vertices),
all vortex-free. This is saturated by entry-cap 100 and **constant through a ~250×
growth** (990 forkless quivers at cap 100 → 249,342 at cap 1600). One-step-beyond
test: mutating every quiver in the cap-900 ball every way (incl. results exceeding the
cap), **0** forkless results escape the 22.

The 22 form a **finite automaton** (states = the 22 patterns; edges = achieved
forkless→forkless transitions `(σ,k) ↦ σ'`): 68 transitions defined, **44
deterministic, 24 nondeterministic** (each nondeterministic `(σ,k)` has 2 outcomes,
**both in the 22**). BFS from `sign(C)` over these transitions reaches exactly the 22.
So the automaton is finite, closed, and complete **on the ball**. Note `4/68`
transitions are "mixed": whether `μ_k(B)` is a fork or forkless is itself
magnitude-dependent there.

## 3. THE REMAINING LEMMA

> **Completeness:** the forkless part of `[C]` realizes *exactly* these 22 sign-patterns
> (equivalently: the achieved forkless transitions stay in the 22 at **all** magnitudes,
> not just on the cap-900 ball). This lemma `⟹ [C] vortex-free ⟹ Goal.`

## 4. Why it's subtle — and what we have

- **Completeness `⟺ R1`.** By the unification, "no 23rd (vortex) pattern in the
  forkless part" is exactly "[C] vortex-free" is exactly (R1). So this is not a strictly
  easier statement — it's (R1) reframed. The value is the *frame*: a finite 22-state
  automaton to be shown closed, which invites a tameness/finite-state argument that the
  raw magnitude form of (R1) did not.
- **The transition is genuinely nondeterministic.** `(σ,k)` does not determine `σ'` —
  it depends on which fireable edges flip (`|b_ij| < |b_ik||b_kj|`), a magnitude
  condition. So a pure sign-automaton is an *over-approximation*, and the
  over-approximation is NOT closed: allowing all flip-subsets from a vortex-free
  tournament can produce a vortex tournament (verified: 48 such 4-vertex cases, ~39k
  5-vertex). Those vortex-patterns are the "dangerous 23rd" states; `[C]` never realizes
  them, but *only because its magnitudes never trigger the escaping flip-subset.* So the
  magnitude constraint is load-bearing and cannot be discarded.
- **What is available:** the forkless part is **connected** (Warkentin: fork-trees hang
  off the forkless core, exit only via the point of return) and **tame** (quadratic
  growth; it is the stratum tree `X_m=(μ₂μ₀)^m C → Y_m=μ₄X_m → Z_m=μ₂Y_m → …`, each
  stratum an affine family with entries linear in one parameter). Also proven earlier:
  the reduction lemmas (coherence, (T), strictness `q≠ap mod 5`, `5∣D` in Case-5c), the
  chain-terminal window dynamics, and the creation taxonomy.

## 5. What we're asking

How would you formalize §3? Candidate lines we see, and want your read on (or a better
one):

1. **Stabilization on the stratum tree.** On each affine family (linear entries), the
   flip-decisions stabilize for large parameter (`|b_ik||b_kj| ~ m²` dominates
   `|b_ij| ~ m`), so the sign-pattern is eventually constant and the transition is
   eventually the "stable" one. If the transient (small-`m`) patterns all appear at
   bounded maxent `≤ M`, and the stable patterns are among the 22, completeness follows.
   Obstacle: there are **infinitely many strata** (the tree branches, leading coefficients
   `~a, 2a, 3a, …`); we need them to realize only finitely many *pattern-types*. Is there
   a clean way to show the stratum-tree recursion is eventually periodic in sign-pattern,
   or otherwise finite-state, without enumerating all strata?

2. **Minimal-maxent counterexample.** If the forkless part realized a 23rd pattern, take
   `B*` forkless with a 23rd pattern of minimal maxent. Its maxent-reducing forkless
   mutation lands on a 22-pattern quiver `B'` (minimality), so `B* = μ_k(B')` — the 23rd
   is a one-step forkless image of a 22-pattern quiver `B'` (possibly large). Reduces
   completeness to: **no 22-pattern forkless quiver has a forkless mutation to a 23rd
   pattern, at any magnitude.** Is there a monotone potential making this a finite check,
   or does `B'` being unbounded defeat it?

3. **Flip-subset enumeration + fork-ness.** For each `σ` in the 22 and each `k`,
   enumerate the flip-subsets `S` of the fireable edges; each gives an outcome pattern
   `σ'(σ,k,S)`. The escaping `σ'` are the vortex tournaments. Can one show that every
   flip-subset `S` producing an escaping `σ'` also forces the result to be a **fork**
   (hence outside the forkless part), or is magnitude-incompatible with `σ` being
   forkless? I.e., is "forkless + this flip-subset" contradictory for the escaping cases?
   This would make the whole thing a finite sign/orientation case-analysis. (Fork-ness is
   magnitude-dependent, so this needs the fork dominance inequalities, not just signs —
   but perhaps the escaping cases are exactly the ones where the point-of-return
   inequalities are forced.)

4. Anything cleaner — a mutation-invariant of the *framed* quiver `(B, C-matrix)`, a
   quasi-Cartan/`𝔽₅` companion argument, or a direct proof that the 22-state NFA is the
   full sign-pattern reachable set.

## 6. RESULT of the experiments (2026-07-06): local approach is DEAD; phantoms exist

- **LP pass (log-linear flip constraints only):** of 392 escaping `(σ,k,S)` triples,
  **0 are infeasible** — the shared `b_ik` variables do not chain into infeasibility.
  (176 escape to vortex patterns, 216 to non-22 vortex-free patterns.)
- **Phantom search:** abstract forkless quivers with a Σ₂₂ sign-pattern whose forkless
  mutation escapes the 22 (incl. to vortex patterns) **exist**, and exist even with all
  entries **abundant (≥2)** — so not a circularity artifact.

⟹ **The One-Step Closure Lemma is FALSE.** No local sign-plus-one-step-magnitude
argument works; `[C]` avoids the phantoms only by a global property. Completeness
(`⟺ R1`) requires the **tameness normal form** (line 1: classify the forkless stratum
families as explicit polynomial families, prove mutation maps family→family) or the
**comparison-abstraction CEGAR** (enrich automaton states with magnitude-comparison
vectors; test whether that is finite-and-closed on `[C]`). The normal form is the robust
route but is a substantial classification project.

## 7. Comparison-abstraction CEGAR result (2026-07-06): also hits the wall, but maps the structure

Enriched state = `(σ, comparison-vector)` where cvec = the 30 flip-predicates
`[|b_ij| < |b_ik||b_kj|]`. On `[C]`'s forkless part: **exactly 110 refined states**,
saturated by cap 100, constant through ~80× growth; closed on the ball (0 escapes);
the **sign-successor `σ'` is deterministic** given `(σ,cvec,k)` (0/332 non-unique),
nondeterminism only in cvec' (≤3 outcomes, all in 110). The refined enrichment
**correctly excludes the sign-phantoms** (their cvec ∉ the 110).

BUT **refined-phantoms exist** — a non-`[C]` forkless quiver with a legitimate 110-state
whose forkless mutation escapes the 110, found after only ~35 samples. So the
110-invariant is not closed over all magnitudes either. The "phantom at every finite
abstraction level" pattern confirms the reachability wall is not finitely abstractable:
`[C]`'s forkless part is a *proper* subset of 110-state quivers, separable from the
refined-phantoms only by the global structure.

**Upshot.** No finite local invariant closes completeness (`⟺ R1`); the robust route is
the **tameness normal form**. But the 110-state, sign-deterministic automaton is the
**finite shadow of the stratum tree**: almost certainly 110 refined states ↔ the stratum
families, deterministic sign-transitions ↔ tropical (leading-coefficient) mutation. The
normal-form proof skeleton: *classify the 110/stratum families explicitly, prove mutation
permutes them via the tropical dynamics, read off that all 22 σ are vortex-free.*

We can run any harness experiment (mutate representatives, enumerate flip-subsets,
compute stratum families, test a proposed stabilization bound `M`, check the
fork-ness/flip-subset correlation of line 3). The verification harness is Python;
`probe17_forkless.mutate(tuple, k, PAIRS, 5)` is the mutation rule, and the cap-1600
component + the 22 patterns + the automaton are computed. Tell us which experiment
would most sharpen the line you'd pursue.
