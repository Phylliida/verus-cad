# Question: a **mutation-abundant, vortex-free** quiver with **infinite forkless part**?

Self-contained statement for a search/proof attempt. All terms defined from
scratch. This is the *clean* form of the infinite-forkless question: our earlier
example `Q₁₄` has infinite forkless part but is **neither** mutation-abundant
(its class contains weight-1 arrows) **nor** vortex-free, so it does not settle
the question the fork/coefficient theory actually cares about.

---

## 1. Definitions

**Quiver.** An `n×n` skew-symmetric integer matrix `B=(b_ij)` (`b_ij=−b_ji`,
`b_ii=0`); `b_ij>0` means `b_ij` arrows `i→j`. The **weight** of the pair `{i,j}`
is `|b_ij|`.

**Mutation.** `μ_k(B)=B'`:
`b'_ij = −b_ij` if `i=k` or `j=k`; else `b'_ij = b_ij + (|b_ik|·b_kj + b_ik·|b_kj|)/2`.
`μ_k` is an involution. The **mutation class** `[B]` = all quivers reachable from
`B` by mutations. Everything below is up to **isomorphism** (vertex relabeling).

**Abundant.** `B` is *abundant* if `|b_ij| ≥ 2` for every pair `i ≠ j`.

**Mutation-abundant.** `B` is *mutation-abundant* if **every** quiver in `[B]` is
abundant — i.e. every weight of every quiver mutation-equivalent to `B` is ≥ 2.
(Burcroff, arXiv 2605.12865, Def. `mu-abundant`.)

**Acyclic.** `B` is *acyclic* if the digraph (`i→j` when `b_ij>0`) has no directed
cycle.

**Fork (Warkentin).** `B` is a *fork* if it is abundant, not acyclic, and has a
vertex `r` (unique *point of return*) with `R⁺={i:b_ri>0}`, `R⁻={j:b_jr>0}` (a
partition of the other vertices) such that the induced subquivers on `R⁺` and on
`R⁻` are acyclic and, for all `i∈R⁺, j∈R⁻`, `b_ij > b_ri` **and** `b_ij > b_jr`.

**Vortex (Fomin, arXiv 2304.11505, Def. 6.2).** A *vortex* is a 4-vertex quiver in
which one vertex — the *apex* — is a source or a sink (its three edges to the
other three vertices are all outgoing, or all incoming), and the other three
vertices support an oriented 3-cycle. `B` is *vortex-free* if no 4-vertex
subquiver (induced on 4 of its vertices) is a vortex.

**Forkless part.** The set of quivers in `[B]` that are **not** forks, up to
isomorphism.

---

## 2. The question

> **Question A (existence).** Does there exist a **mutation-abundant** quiver `B`
> (of any rank `n ≥ 3`) whose **forkless part is infinite** — i.e. `[B]` contains
> infinitely many pairwise non-isomorphic non-forks — and, ideally, such that `B`
> (and every quiver in its forkless part) is **vortex-free**?
>
> **Question B (the likely-clean dichotomy).** Prove or disprove: *if `B` is
> mutation-abundant, then its forkless part is finite.* (Optionally with the extra
> hypothesis "and vortex-free" / "and complete", matching the regime of Cyclically
> Ordered Quivers, arXiv 2406.03604, and Burcroff, arXiv 2605.12865, where finite
> forkless part is established for several such families.)

A positive answer to A, or a counterexample to B, would be the first
**mutation-abundant** class with infinite forkless part — the open (infinite)
side of Burcroff's stated open problem ("give a criterion for finite
ice-forkless part"), *inside* the regime where finiteness was expected. A proof
of B would be a clean structural theorem: mutation-abundance ⇒ finite forkless
core ⇒ (given decidable membership) decidable mutation equivalence for such
classes.

---

## 3. What is already known (do not re-derive)

- **Infinite forkless part exists in general** (not mutation-abundant): the class
  of `Q₁₄=[-2,-2,2,-2,-2,-2,1,2,1,2]` (upper entries) is infinite-forkless, via the
  explicit family `N_m=(μ₃μ₀)^m(Q₁₄)` which keeps a weight-1 arrow `b₁₄=1` forever
  (so every `N_m` is non-abundant ⇒ non-fork). **This exploits non-abundance and
  does not answer Question A.** `Q₁₄` itself has a vortex (apex 2, cycle on
  {0,1,3}) and its class is not mutation-abundant.
- Even the *abundant* non-forks in `[Q₁₄]` are infinite: `Q^{(m)}=μ₀μ₁(μ₃μ₀)^m(Q₁₄)`
  are abundant, non-acyclic, vortex-free non-forks (no point of return). But
  `[Q₁₄]` as a whole is **not** mutation-abundant (it also contains the `N_m`), so
  this still does not answer A.
- Finite forkless part is known for several **mutation-abundant** families:
  Cyclically Ordered Quivers Ex. 5.13; Fomin "Long mutation cycles" Ex. 10.1–10.2;
  Fordy–Marsh periodic quivers; and Markov-type quivers (each has a *unique*
  forkless quiver). Whether *all* mutation-abundant classes have finite forkless
  part is **open** (Burcroff, §"Finite Ice-Forkless Part").
- Mechanics of forks (Warkentin): mutating a fork at any non-point-of-return
  vertex yields a larger fork; so the mutation graph is a finite forkless core
  with infinite fork-trees attached. Infinite forkless part ⇔ that core is
  infinite. For a mutation-abundant class the forkless part consists of *abundant*
  non-forks only (since all quivers are abundant).

---

## 4. Suggested attack

**Toward A (find an example).** Seek a mutation-abundant class containing an
infinite family of *abundant* non-forks. A promising shape (cf. the `Q^{(m)}`
mechanism, but requiring the *whole class* to stay abundant): a short mutation
word `w` acting *affinely* on some quiver `A` (constant per-step increments) such
that every `w^m(A)` is abundant, non-acyclic, and fails the point-of-return
condition at every vertex, while the whole class `[A]` never produces a weight
`<2`. The obstruction to overcome versus `Q₁₄` is precisely keeping *all* weights
`≥2` throughout the class, not just along one hairpin.

**Toward B (prove finiteness).** In a mutation-abundant class every quiver is
either a fork or a bounded-complexity non-fork; Warkentin's fork/point-of-return
machinery plus (if assumed) vortex-freeness may bound the entries of non-forks. A
proof that abundant + vortex-free (+ complete) non-forks in one class have
bounded weight would give finiteness. The COQ / Burcroff finiteness proofs for
specific families are the model to generalize.

**Computational search** (being run in parallel): enumerate/sample *complete
abundant* rank-4 and rank-5 quivers; keep those with no weight `<2` reachable
within a large entry cap (mutation-abundant candidates) that are vortex-free;
measure whether the count of non-forks (up to isomorphism) with `max|b_ij| ≤ t`
plateaus (finite ⇒ evidence for B) or grows (candidate for A). A calibrated
detector: a mutation-acyclic quiver has forkless-count `= 1` (constant); Q₁₄'s
grows `~t²`.

**Non-goals.** Neither answer bears on undecidability; and "infinite forkless
part" is nowhere conjectured impossible for mutation-abundant classes — B is
genuinely open.

---

## 5. ★ Concrete candidate for Question A (reduced problem)

Computation has produced a **strong candidate**; the hard half (infinite forkless)
is already proven, leaving a focused lemma for a prover.

**Candidate `C`** (upper entries `b_01,…,b_34`): `(-3,-2,-2,2,-2,2,-3,3,-2,-2)`, i.e.
```
        0    1    2    3    4
   0 [  0    3    2    2   -2 ]
   1 [ -3    0    2   -2    3 ]
   2 [ -2   -2    0   -3   -2 ]
   3 [ -2    2    3    0    2 ]
   4 [  2   -3    2   -2    0 ]
```

**Already proven [verified].** The word `w = μ₂μ₀` is a *linear hairpin*:
`w^m(C)` changes only `b_01, b_03, b_12` (by `+10m`) and `b_23` (by `−10m`), fixing
the other six entries `(b_02,b_04,b_13,b_14,b_24,b_34) = (-2,2,2,-3,-2,-2)`, all of
absolute value ≥ 2. Every `w^m(C)` is therefore abundant; and each is **vortex-free
and not a fork** (checked m=0..300; the linear closed form gives a one-line
induction as for Q₁₄). Hence **`[C]` contains infinitely many pairwise
non-isomorphic abundant vortex-free non-forks** — its forkless part is infinite.

**Errata (verify from the TUPLE, not a matrix).** The authoritative object is the
tuple above with `w=μ₂μ₀` meaning *apply μ₀ first*. The pinned six entries are
`(b_02,b_04,b_13,b_14,b_24,b_34) = (-2,2,2,3,-2,2)` (a prior draft had sign slips at
`b_14,b_34` and an inconsistent displayed matrix at `b_24`). The family is affine
only for `m ≥ 1` (the first step `C→w(C)` has increments `+10,+10,+4,-6`; exactly
`±10` thereafter). Independently re-verified by the prover: `X_m=w^m(C)` non-fork
+ vortex-free for all `m`, every point-of-return failing by a *non-strict* tie on a
pinned weight-2 edge.

**Structure of the forkless core (prover).** It is NOT just the hairpin + fork-trees.
`μ₁(X_m),μ₃(X_m)` are forks (pruned), but `μ₄(X_m)=Y_m` and `μ₂(Y_m)=Z_m` are
further abundant, vortex-free non-fork strata, with leading weights `~2a` (`a=10m-3`)
— strata proliferate like the `Q^{(m)}` family. So closure-by-finite-stratification
is not viable; a uniform certificate is needed.

**The reduced problem (what remains to answer A).** Prove:
1. **`C` is mutation-abundant** — no quiver in `[C]` has a weight `< 2`. ★ **Strong
   candidate certificate: mod-5 rigidity.** Every entry of every quiver in `[C]` is
   `≡ ±2 (mod 5)` — verified on the **entire component up to cap 600 (39,440
   quivers)**. Since residues `{2,3}` exclude `{0,1,4}` (the residues of `0,±1`),
   *any* integer `≡ ±2 (mod 5)` has `|·| ≥ 2` — so this property, if mutation-closed
   on `[C]`, **immediately proves (1)**, replacing the even-sector lemma. It is not
   closed on all quivers (the adjustment `b_ik b_kj ≡ (±2)(±2) ≡ ±1 (mod 5)` could
   send `2↦1`), so the focused lemma is a *coherence* condition. Writing
   `b_ij ≡ 2ε_ij (mod 5)` with `ε_ij∈{±1}` (note `{2,3}` are the quadratic
   non-residues mod 5), the adjustment preserves the property iff, whenever it fires
   at `(i,j)` through `k` (so `σ:=sgn b_ik = sgn b_kj`):
   `σ · ε_ik · ε_kj = -ε_ij`.
   **Focused lemma:** this coherence relation is mutation-invariant on `[C]`. (Holds
   empirically throughout; likely a condition on residues around 3-cycles, since the
   naive vertex-gauge `ε_ij = t_ij u_i u_j` already fails at `C`.)
2. **The forkless part of `[C]` is vortex-free** — no non-fork in `[C]` contains a
   vortex. (Verified up to cap 180.) Prover's route: each non-fork stratum found has
   *constant-in-m sign pattern*, so vortex-freeness is a finite check per stratum;
   need a lemma bounding the number of sign patterns of non-forks in `[C]` (plausibly
   also from the mod-5/orientation structure).

Either a proof of (1)+(2) [⇒ **first mutation-abundant vortex-free class with
infinite forkless part**, answering A and refuting "vortex-free ⇒ finite"], or a
demonstration that (1) or (2) *fails* at some larger entry [⇒ `C` is a near-miss,
and Question A / Question B remain open], is decisive and valuable.

For context, an *all-even* mutation-abundant example **with a vortex** and infinite
forkless part is fully in hand: `Q' = (-2,-2,2,-2,-2,-2,2,2,2,2)` with hairpin
`μ₃μ₀` (the `N'_m` are abundant non-forks, `b_14=b_24=2` pinned). The even-sector
lemma gives its mutation-abundance cleanly; only vortex-freeness fails for `Q'`.
