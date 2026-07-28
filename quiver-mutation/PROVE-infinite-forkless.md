# Claim to prove: a rank-5 quiver with **infinite forkless part**

Self-contained problem statement for a proof attempt. All definitions given from
scratch. The goal is a rigorous proof (not computation) of one clean statement.

---

## 1. Definitions

**Quiver.** A quiver on `n` vertices `{0,…,n−1}` is a skew-symmetric integer
matrix `B = (b_ij)` (`b_ij = −b_ji`, `b_ii = 0`). Read `b_ij > 0` as `b_ij` arrows
`i → j`. Here `n = 5`.

**Mutation.** For a vertex `k`, the mutated quiver `μ_k(B) = B'` is
```
b'_ij = −b_ij                                   if i = k or j = k,
b'_ij = b_ij + ( |b_ik|·b_kj + b_ik·|b_kj| ) / 2   otherwise.
```
`μ_k` is an involution. The **mutation class** `[B]` is the set of all quivers
reachable from `B` by finite sequences of mutations.

**Isomorphism.** Quivers `B, B'` are isomorphic (`B ≅ B'`) if `B'_{ij} =
B_{σ(i)σ(j)}` for some permutation `σ` of the vertices. Mutation classes and all
notions below are considered **up to isomorphism**.

**Abundant.** `B` is *abundant* if `|b_ij| ≥ 2` for every pair `i ≠ j`.

**Acyclic.** `B` is *acyclic* if the directed graph (`i → j` when `b_ij > 0`) has
no directed cycle.

**Fork (Warkentin).** `B` is a *fork* if it is abundant, not acyclic, and has a
vertex `r` (the *point of return*) such that, writing
`R⁺ = {i : b_ri > 0}` and `R⁻ = {j : b_jr > 0}` (so `R⁺, R⁻` partition the other
four vertices),
- the full subquivers induced on `R⁺` and on `R⁻` are each acyclic, and
- for all `i ∈ R⁺`, `j ∈ R⁻`:  `b_ij > b_ri`  **and**  `b_ij > b_jr`.

(The point of return, if it exists, is unique.)

**Forkless part.** The *forkless part* of `[B]` is the set of quivers in `[B]`
that are **not** forks, counted up to isomorphism.

---

## 2. The claim

> **Claim (target).** The mutation class of the quiver `Q₁₄` below has an
> **infinite forkless part**: it contains infinitely many pairwise
> non-isomorphic quivers that are not forks.

**`Q₁₄`** (upper entries `b_01,b_02,b_03,b_04,b_12,b_13,b_14,b_23,b_24,b_34`):
```
[ -2, -2,  2, -2, -2, -2,  1,  2,  1,  2 ]
```
i.e.
```
        0    1    2    3    4
   0 [  0   -2   -2    2   -2 ]
   1 [  2    0   -2   -2    1 ]
   2 [  2    2    0    2    1 ]
   3 [ -2    2   -2    0    2 ]
   4 [  2   -1   -1   -2    0 ]
```
`Q₁₄` is mutation-cyclic (not mutation-equivalent to any acyclic quiver;
certified via the "totally proper" obstruction of Neville, arXiv 2409.17832 —
`Q₁₄` is not totally proper).

Any one of the following four alternatives is an equally acceptable target (each
shows the same phenomenon; `Q₁₄, Q₁₅` have the strongest evidence):
```
Q9  = [ 0,-1, 0, 2,-1, 3,-3, 2, 2, 3 ]
Q13 = [ 2,-2,-1, 2,-1, 0,-2, 2, 0,-2 ]
Q15 = [ 2,-2, 2,-2, 2, 1,-1, 2, 2,-2 ]
Q19 = [-2, 0, 0,-2,-2,-1, 2, 2, 1,-2 ]
```

---

## 3. What is known / suggested proof route

**Computational evidence (not a proof).** Enumerating `[Q₁₄]` restricted to
quivers with `max|entry| ≤ t`, the number of non-fork quivers (up to
isomorphism) with `max|entry| ≤ t` grows **without visible bound** — roughly
**quadratically** in `t` (e.g. ≈ 227, 1034, 2284, 6228, 8912, 24150 at
`t = 20,40,60,100,120,200`), against a mutation-acyclic control whose count is
constant `= 1`. A second, independent fork-detector (`forkWithPOR` from the
"Mathematicians vs Machines" database) agrees with the above on 4000/4000 tested
quivers, so the growth is not a detection artifact.

**Structure of the growing non-forks.** The overwhelming majority of the
non-fork quivers found are **abundant and non-acyclic** yet fail the
point-of-return condition (7036 of 8912 at `t = 120`). So the mechanism is *not*
non-abundance; it is genuine abundant, non-acyclic quivers with **no valid point
of return**.

**Suggested route (Fomin-style, but on the infinite side).** Exhibit an explicit
infinite family `F_m` (`m ≥ 1`) and prove:
1. **Membership:** each `F_m ∈ [Q₁₄]` — e.g. give an explicit mutation word
   `w_m` (ideally with a recursive/periodic structure so `w_{m+1}` extends
   `w_m`) taking `Q₁₄` to `F_m`. (Cf. the parametric mutation-word constructions
   in Fomin, "Long mutation cycles", arXiv 2304.11505.)
2. **Not a fork:** each `F_m` is abundant and non-acyclic but has **no** vertex
   `r` satisfying the fork inequalities — e.g. show that for every candidate `r`
   there exist `i ∈ R⁺(r)`, `j ∈ R⁻(r)` with `b_ij ≤ b_ri` or `b_ij ≤ b_jr`, or
   that some induced subquiver `R±(r)` has a cycle.
3. **Pairwise non-isomorphic / unbounded:** the `F_m` are pairwise
   non-isomorphic, e.g. because `max|entry|(F_m) → ∞` while their entry
   multisets differ (an isomorphism-invariant such as the sorted multiset of
   `|b_ij|` suffices).

Then `{F_m}` is an infinite set of pairwise non-isomorphic non-forks in `[Q₁₄]`,
proving the Claim.

**Weaker but still valuable variants** (any of these is a real result):
- Prove the forkless part of *some* explicit rank-`n` mutation-cyclic quiver is
  infinite (existence; `n` may be chosen `> 5` if that makes the family cleaner).
- Prove an infinite family of **abundant non-acyclic non-forks** exists inside
  one mutation class (this is the crux; membership + non-fork is the substance).

---

## 4. Context (why this is worth proving)

Burcroff (arXiv 2605.12865, §"Finite Ice-Forkless Part") states it is an **open
problem** to characterize which mutation classes have finite forkless part.
Finite examples are known (COQ arXiv 2406.03604 Ex 5.13; Fomin arXiv 2304.11505
Ex 10.1–10.2; Fordy–Marsh). An **explicit infinite** example appears not to be
recorded; proving the Claim supplies one, on the open (infinite) side of that
criterion. It also pins down, for the decidability of quiver mutation
equivalence, a class where Warkentin fork-descent provably does not terminate to
a finite core — isolating exactly where a different decision method is required.

**Non-goals / cautions.** Infinite forkless part does **not** imply the mutation
class is undecidable, and does **not** contradict any published conjecture (the
finiteness is nowhere conjectured to be universal). The target is purely the
combinatorial statement in §2.
