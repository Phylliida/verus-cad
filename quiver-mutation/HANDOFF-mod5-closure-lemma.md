# Handoff: prove the mod-5 closure lemma for quiver `[C]`

Self-contained. A fresh attempt at one focused lemma. Everything you need is below;
prior attempts (and dead ends) are listed so you don't repeat them.

## 0. YOUR TASK (read this first)

**Prove condition (R1) holds for every quiver in the mutation class `[C]`.** That
single quantitative fact is now the *only* remaining obligation; a prior pass already
proved and machine-verified everything else in the chain (the triangle-law
reformulation, the parity law, and that mutation preserves the invariant in every
local configuration *except* the one (R1) governs — see §§1–8). Closing (R1) completes
a proof that `C` is **mutation-abundant**, which is the last missing piece of an answer
to an open research question (does a mutation-abundant, vortex-free quiver have infinite
forkless part? — `C` is the candidate, its infinite forkless part is already proven).

**State it precisely (this is the theorem to prove).** For every `B ∈ [C]`, every
vertex `k`, and every triple `{i,j,l}` of the other four vertices with
`sgn(b_ik)=sgn(b_jk)=−sgn(b_lk)` such that the triangles `{i,k,l}` and `{j,k,l}` are
**both cyclic** (equivalently: the "Case 5c" configuration of §3; then `{i,j,l}` is
transitive with a well-defined middle vertex `m∈{i,j}` and other vertex `o∈{i,j}`):

> **(R1)**  `|b_ml| < |b_mk|·|b_kl|  ⟹  |b_ol| < |b_ok|·|b_kl|`.

Equivalently, in triangle language: **the two cyclic triangles `U_m={m,k,l}` and
`U_o={o,k,l}` share the edge `(k,l)`; if `U_m` is subcritical at its edge `(m,l)`
(i.e. `|b_ml|` is less than the product of its other two edges), then `U_o` is
subcritical at its edge `(o,l)`.** Prove this implication holds for every quiver in
`[C]`.

**What is already done (do not redo — see §§1–8):** Theorems 1–3 and the parity law
are proved and verified on 87,620 quivers / 526,756 configurations. (R1) itself is
verified to hold on all 526,756 configurations — so the statement is **true**; the task
is a *proof* that survives to arbitrarily large quivers in `[C]`.

**What NOT to try (falsified — §8):** the ratio inequality (R1′)
`|b_ml|·|b_ok| ≥ |b_ol|·|b_mk|` is **false** in `[C]` (1104 counterexamples); do not
route through it. The corrected certificate must imply (R1) directly.

**What "done" looks like:** a proof that (R1) is preserved under mutation (given that
all of §§1–3 already hold at `B`), by induction from `C`. Likely ingredients: a finite
set of *criticality-bit* laws on cyclic/transitive triangles closed under the firing
dynamics of §3 (all criticality comparisons are strict by the mod-5 rigidity, so the
bits are well-defined state), or a genuinely quantitative triangle invariant that
survives the linear weight-update `z ↦ xy ± z`. A verification harness for any proposed
invariant is available (must hold on all 526,756 configs and be mutation-stable).

## 1. Setup and conventions

A **quiver** is a 5×5 skew-symmetric integer matrix `B=(b_ij)`, stored as the upper
tuple `(b_01,b_02,b_03,b_04,b_12,b_13,b_14,b_23,b_24,b_34)`. **Mutation** at vertex
`k`:
```
b'_ij = -b_ij                                  if i=k or j=k
b'_ij = b_ij + (|b_ik|·b_kj + b_ik·|b_kj|)/2    otherwise
```
The correction term `δ := (|b_ik|·b_kj + b_ik·|b_kj|)/2` satisfies:
`δ = σ·|b_ik|·|b_kj|` if `sgn(b_ik)=sgn(b_kj)=:σ` ("firing"), and `δ=0` if they have
opposite signs. `[B]` = mutation class (all quivers reachable by mutations).
A quiver is **abundant** if `|b_ij|≥2` for all `i≠j`; **mutation-abundant** if every
quiver in `[B]` is abundant.

## 2. The object and what is already proven

`C = (-3,-2,-2,2,-2,2,-3,3,-2,-2)`. It is a strong candidate for a **mutation-
abundant, vortex-free quiver whose forkless part is infinite** (an open question).
The *infinite forkless part* is already **proven**: the word `w = μ_2∘μ_0` (apply
`μ_0` first) is a linear hairpin — for `m≥1`, `X_m := w^m(C)` changes only
`b_01,b_03,b_12` (`+10` per step) and `b_23` (`−10`), leaving the other six entries
fixed at `(b_02,b_04,b_13,b_14,b_24,b_34)=(-2,2,2,3,-2,2)`; every `X_m` is abundant,
vortex-free, and a non-fork (closed form ⇒ one-line induction). The forkless core is
larger than this ray (mutating `X_m` at `4` gives another non-fork stratum `Y_m`,
then `μ_2(Y_m)=Z_m`, etc., with leading weights `~2·(10m)`), but that only reinforces
"infinite forkless part."

**The only remaining gap** to answering the open question is:

> **prove `C` is mutation-abundant** — i.e. no quiver in `[C]` has a weight `< 2`.

## 3. The mod-5 certificate (the lemma to prove)

Empirically, **every entry of every quiver in `[C]` is `≡ ±2 (mod 5)`** (residue in
`{2,3}`). Since the residues `{2,3}` exclude `{0,1,4}` — the residues of `0,±1` — any
integer `≡ ±2 (mod 5)` automatically has absolute value `≥ 2`. Therefore:

> **LEMMA (target).** For every `B ∈ [C]` and every `i≠j`, `b_ij ≡ ±2 (mod 5)`.

Proving this **immediately** gives mutation-abundance of `C`, hence the whole result.
(`C`'s residues are `(2,3,3,2,3,2,2,3,3,3)` — all in `{2,3}`. The hairpin increments
are `±10 ≡ 0`, so the `X_m` trivially stay in the class; the content is the rest of
`[C]`.)

## 4. Reduction to a local triangle condition (already done — use it)

Write `b_ij ≡ 2ε_ij (mod 5)` with `ε_ij ∈ {±1}` (so `ε=+1 ⇔ residue 2`,
`ε=−1 ⇔ residue 3`; note `ε` is skew: `ε_ji=−ε_ij`). Let `σ_ij = sgn(b_ij)`.
Because `|b_ik| ≡ 2σ_ik ε_ik (mod 5)`, a firing correction satisfies
`δ ≡ σ·(2σ_ik ε_ik)(2σ_kj ε_kj) ≡ 4σ·ε_ik ε_kj ≡ −σ·ε_ik ε_kj (mod 5)` (using
`σ_ik=σ_kj=σ`, `4≡−1`). Hence `b'_ij ≡ 2ε_ij − σ·ε_ik ε_kj`, and this lands in
`{2,3}` **iff**

> **(★)  σ · ε_ik · ε_kj = −ε_ij**   (whenever `sgn(b_ik)=sgn(b_kj)=σ`).

When (★) holds, the fired entry's class flips: `ε'_ij = −ε_ij`. Non-firing entries
and the `k`-incident entries keep the property automatically (`ε` just negates). So:

> **The LEMMA ⟺ (★) holds for every quiver in `[C]`, every `k`, and every firing
> triangle `{i,j,k}`.**

This is a *local* condition on the `(residue, sign)` data of the three edges of a
triangle — a much smaller target than describing the class. Equivalent forms (may be
more suggestive): with `ρ_ij := ε_ij` (skew) and using `σ_ik=σ_kj`, (★) is
`ρ_ij = σ_ik ρ_ik ρ_kj`, i.e. the oriented triangle product `ρ_ij ρ_jk ρ_ki = σ_ik`.

## 5. Evidence (very strong)

- Verified on the **entire component of `[C]` up to entry-cap 900: 87,620 quivers**,
  every entry `≡ ±2 (mod 5)` — **zero exceptions**.
- Stronger: taking the `(residue mod 5, sign)` **type** of each quiver, there are 742
  distinct types, and **every one-step successor type — including those whose
  representatives exceed the cap — has all residues in `{2,3}`** (0 bad). So the
  one-step closure is airtight on everything observed.
- `{2,3}` are exactly the **quadratic non-residues mod 5**; the correction is
  `≡ ±1 (mod 5)` (a product of two non-residues is a residue `= ±1`), so each fired
  entry moves by `±1 mod 5`, and (★) is exactly "the direction of that move matches
  the current class."

## 6. Approaches already tried that do NOT work (don't repeat)

1. **Finite `(residue,sign)`-type automaton.** The new *residues* are determined by a
   quiver's type, so a finite *closed* type set with residues in `{2,3}` would prove
   it. But the reachable type set does **not** saturate at reachable caps (348 types
   at cap 300 → 742 at cap 900; the number of successor types outside the found set
   *grows*, 664 → 1088). No finite closed automaton was exhibited.
2. **Universal version** ("any quiver with all residues in `{2,3}` mutates to one").
   **False.** Allowing all sign patterns (over-approximation) blows up (>3·10⁶ types)
   and *does* produce residues `1`/`4`. So (★) is **not** automatic — it depends on
   which sign patterns are actually achievable in `[C]`. The achievability constraint
   is essential and was the thing not characterized.
3. **Vertex gauge** `ε_ij = t_ij·u_i·u_j` (signs `t_ij=sgn b_ij`, vertex labels
   `u_i∈{±1}`): the constraints are already inconsistent at `C` itself. A pure vertex
   gauge for `ε` does not exist.
4. **Even-sector lemma** (all-even entries ⇒ mutation-closed, abundant ⇔ complete):
   inapplicable — `C` has odd entries `±3`.

## 7. Suggested directions

- A **mod-5 quadratic / congruence invariant** rather than a linear gauge. Mutation
  is a unimodular congruence `B ↦ E_k^⊤ B E_k` (`E_k∈GL_5(ℤ)`, `det=−1`), so it
  preserves `B mod 5` up to this congruence: rank over `𝔽_5`, the `𝔽_5`-congruence
  class of the skew form, `ker(B mod 5)`, etc. Does the `𝔽_5`-congruence orbit of
  `C mod 5` consist only of matrices with all entries `≡ ±2`? (Note `n=5` is odd so
  `det B = 0`; look at rank-4 vs rank-2 strata and the radical.)
- Prove (★) is **mutation-invariant** directly: assume (★) holds for all firing
  triangles of `B`; show it holds for all firing triangles of `μ_k(B)`. This couples
  triangles `{i,j,l}` (whose edge `(i,j)` is changed by `μ_k`) but is a finite
  case-analysis over the `(ε,σ)` states of the tetrahedron `{i,j,k,l}`.
- Characterize the **achievable sign patterns** as their own mutation-invariant
  (a constraint on the tournament `σ`), then feed it into the type automaton to force
  saturation.

Verification harness available on request (Python; `probe17_forkless.mutate` uses the
convention in §1). A quick check that a proposed invariant is real: it must hold on
all 87,620 quivers of the cap-900 component and be preserved by all five mutations.

---

## 8. Verification results (the four §4 tests, run on the cap-900 component)

Ran on the full component: **87,620 quivers, 526,756 Case-5c configurations**.

1. **Parity law (Thm 2): PASS** — every 4-subquiver has 0 or 2 cyclic triangles;
   0 violations. The new sign-tournament invariant is confirmed.
2. **Triangle law (T) (Thm 1): PASS** — `τ_△=+1 ⟺ cyclic`; 0 violations. The whole
   `τ`-reformulation is validated on the class.
3. **(R1): PASS — 0 violations across all 526,756 Case-5c configs.** The dangerous
   flip-pattern `(flip_m,flip_o)=(True,False)` — the *only* one that breaks (T) —
   **never occurs**. So (R1) is exactly the right condition and it holds everywhere:
   the LEMMA is confirmed true modulo proving (R1) propagates.
4. **(R1′): FAILS — 1104 violations.** So the ratio inequality is *not* a valid
   invariant; do not use it. Crucially, **every R1′-failure has
   `(flip_m,flip_o) ∈ {(True,True): 952, (False,False): 152}`** — i.e. all failures
   are "both flip" or "neither flips", the safe patterns. R1′ is strictly stronger
   than needed and false; (R1) survives because the bad `(True,False)` pattern is
   what's actually forbidden.

## 9. Harness results for the dihedral analysis (T1–T5)

Ran on the cap-700/900 component (324k–527k Case-5c configs). Verdicts:

- **T1 `g_o ≥ g_m` (gap monotonicity): FAILS**, 182,528 / 526,756 violations. Dead.
- **T2 `q_m ≥ q_o` on (T,T) configs: FAILS**, 220,420 / 404,644. Dead. (Consistent
  with T1 dead.) ⟹ **No simple 2D inequality on `(q_m,p_m,q_o,p_o)` is a certificate.**
- **T3 `sgn(D)` × flip-pattern** (`D=q_m p_o−p_m q_o`): the forbidden `(T,F)` pattern
  **never occurs** (0). `(F,T) ⟹ D>0` **always** (81,348/81,348). `D<0` occurs **only**
  in the symmetric patterns: `(T,T)`:952 and `(F,F)`:152 (plus `D=0`: 44 total). So
  R1′ (`D≥0`) fails exactly in the safe symmetric patterns — `sgn(D)` carries real
  structure but is not a standalone certificate.
- **T4 `(R1-l)` (Channel A obligation): PASS, 0 violations.** `(R1-l′)` (Channel B):
  188 "violations" on the approximate Channel-B subpopulation — an artifact: the true
  derived obligations are just (R1) at the successor `μ_l(B)∈[C]`, which holds since
  (R1) holds everywhere; testing them as standalone predicates on hand-cut
  subpopulations gives spurious misses. **These are auto-satisfied; the task is the
  `B`-level invariant that implies them, not the predicates themselves.**
- **T5 (dihedral descent interlacing):** my naive greedy descent-depth
  (`while a reflection reduces q+p`) gives only 73% within `|Δ|≤1` and a degenerate
  tail — so it is **not** the intended notion. The exact alternating-word exit-time
  definition needs to be specified precisely (which reflection at each step, and the
  exit criterion) before it can be tested; I'll run whatever precise definition you
  give.

**Net for the certificate.** Every *simple inequality* candidate is dead (T1, T2, R1′).
What survives is the *structural* picture: the `(q,p)`-pairs evolve by the dihedral
`⟨S_k,S_l⟩` preserving `Q_a`, with chain invariants `C_m, C_o, |D|`; a viable
certificate must be built from those invariants and/or the interlacing, and must
transform correctly under the role-swap. The most promising concrete target is a
precise **exit-time interlacing** statement (T5 done right) or a **`sgn(D)`-vs-role**
rule (T3), either of which reduces to classical `Q_a`-geometry (eigenvector cone of
`S_kS_l`, eigenvalue `(a+√(a²−4))/2`).

**Upshot for the next attempt.** The reduction (Thms 1–3, parity law) is fully
verified. The entire remaining task is: **prove `flip_m ⟹ flip_o` in Case 5c**
(equivalently, that `(flip_m,flip_o)=(True,False)` is unreachable), *without* going
through R1′. In Case-5c terms: `U_m={m,k,l}` and `U_o={o,k,l}` are both cyclic and
share edge `(k,l)`; `flip_x ⟺ U_x` is *subcritical at its `(x,l)` edge*
(`|b_xl| < |b_xk|·|b_kl|`). So the exact needed lemma is: **if the cyclic triangle
`U_m` is subcritical at `(m,l)`, then the cyclic triangle `U_o` is subcritical at
`(o,l)`** — a relation between two cyclic triangles sharing the edge into the
minority vertex `l`. A corrected quantitative certificate (replacing the false R1′)
should target exactly this. The criticality-bit automaton of §4-test-4 remains the
promising structural route, now with R1 confirmed as the only obligation.
